import PptFactorization.AppendixBUpperBoundClosure
import PptFactorization.AristotleTargets.LowerNoInputsConcreteChoices
import PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices

/-!
Upper endpoint assembled from the concrete lower one-column pipeline.

This file is a bridge file: it does not introduce new probability estimates.
It connects the current upper endpoint to the already audited lower-side
canonical column suppliers, so that `hColumnIncluded`, `hCap`, and
`hBackgroundHalf` are no longer theorem-facing inputs on this route.
-/

namespace AppendixB

open Filter
open PptFactorization.RandomMatrixModel
open scoped Topology Matrix.Norms.Frobenius

/-- Spherical auto-height-band input used by the average-gain upper endpoint.

Plainly: among half-mass competitors on the finite real sphere, the
neighbourhood complement comparison can be converted into a rectangular
polarization block with average gain controlled by the polarization objective.
This is the geometric input behind the `lemma43AutoHeightBands` parameter; the
definition gives it a readable theorem-facing name rather than leaving its full
quantifier block inline. -/
def finRealSphereAutoHeightBandsAverageGainSup : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ epsBand tauSep : ℝ,
          0 < epsBand ∧
            0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel pole a tauMax,
                  0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                          Cmodel =
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                          A ∧
                        epsBand ≤
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                            (symmDiff Cmodel A) ∧
                          ∀ ⦃tauBand : ℝ⦄,
                            0 < tauBand → tauBand ≤ tauMax →
                              ∃ avg : ℝ,
                                SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                  n tauSep
                                  (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                    Cmodel A
                                    (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                      n pole a tauBand))
                                  (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                    Cmodel A
                                    (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                      n pole a tauBand))
                                  avg ∧
                                avg ≤
                                  sSup
                                    (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                      n r A)

/-- The named geometric input is definitionally the raw endpoint input. -/
theorem finRealSphereAutoHeightBandsAverageGainSup_iff_raw :
    finRealSphereAutoHeightBandsAverageGainSup ↔
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A) := by
  rfl

/-- Turn the named geometric input into the raw endpoint form. -/
theorem finRealSphereAutoHeightBandsAverageGainSup.raw
    (hGeom : finRealSphereAutoHeightBandsAverageGainSup) :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A) :=
  finRealSphereAutoHeightBandsAverageGainSup_iff_raw.1 hGeom

/-- The auto-height-band geometric input is strong enough to recover the
half-measure hemisphere comparison in dimensions at least two.

Plainly: this input is not a harmless transport lemma.  Once supplied, the
existing polarization proof derives the cap-comparison statement that
hemispheres maximize the complement of the `r`-neighbourhood among half-mass
competitors.  The remaining work behind this input is therefore the
spherical-polarization/symmetrization theorem, not mathlib limit arithmetic. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_finRealSphereAutoHeightBandsAverageGainSup
    (hGeom : finRealSphereAutoHeightBandsAverageGainSup) :
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo := by
  exact
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparisonGeTwo_of_lemma43_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hGeom)

/-- The auto-height-band geometric input supplies the global half-measure
hemisphere comparison.

The nontrivial dimensions `n >= 2` come from the auto-height-band/polarization
packet; the one-dimensional sphere is handled by the existing elementary
adapter.  This still does not include the separate Gaussian tail needed for
full spherical isoperimetry. -/
theorem sphere_halfMeasure_hemisphereComparison_of_finRealSphereAutoHeightBandsAverageGainSup
    (hGeom : finRealSphereAutoHeightBandsAverageGainSup) :
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison := by
  exact
    PptFactorization.AppendixB.sphere_halfMeasure_hemisphereComparison_of_geTwo
      (sphere_halfMeasure_hemisphereComparisonGeTwo_of_finRealSphereAutoHeightBandsAverageGainSup
        hGeom)

/-- The auto-height-band geometric input plus the checked cap-cone flattening
tail supplies the full spherical isoperimetry package.

Plainly: the cap-comparison side is the auto-height-band/polarization theorem,
and the Gaussian tail side is no longer an extra hypothesis on this route; it
is supplied by the existing cap-cone flattening-map construction. -/
theorem fullSphericalIsoperimetry_of_finRealSphereAutoHeightBandsAverageGainSup_capConeFlatteningMap
    (hGeom : finRealSphereAutoHeightBandsAverageGainSup) :
    PptFactorization.AppendixB.FullSphericalIsoperimetry := by
  exact
    fullSphericalIsoperimetry_of_lemma43AutoHeightBands_northPoleCapConeGaussianTailLargeExponent
      (finRealSphereAutoHeightBandsAverageGainSup.raw hGeom)
      (PptFactorization.AppendixB.sphere_northPoleCapConeGaussianTailLargeExponent_of_cosinePowerTailBelowHalf
        PptFactorization.AppendixB.sphere_northPoleCapConeCosinePowerTailBelowHalf_from_capConeFlatteningMap)

/-- The same route supplies the exact cap-minimization/isoperimetry target.

This is a naming adapter: after the cap-cone Gaussian tail is supplied by the
flattening-map construction, the only remaining geometric input is the
auto-height-band comparison itself. -/
theorem sphere_caps_minimize_neighborhoods_of_finRealSphereAutoHeightBandsAverageGainSup_capConeFlatteningMap
    (hGeom : finRealSphereAutoHeightBandsAverageGainSup) :
    PptFactorization.AppendixB.sphere_caps_minimize_neighborhoods :=
  fullSphericalIsoperimetry_of_finRealSphereAutoHeightBandsAverageGainSup_capConeFlatteningMap
    hGeom

/-- The cleaned endpoint's geometry input supplies the concrete-family
isoperimetry statement used for spherical concentration.

This isolates the part of the geometric packet that is pure spherical
isoperimetry.  The auto-height-band input is still stronger than this
consequence: it is also the polarization mechanism used by the route. -/
theorem eventually_upper_hIso_concreteModel_of_finRealSphereAutoHeightBandsAverageGainSup
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hGeom : finRealSphereAutoHeightBandsAverageGainSup) :
    ∀ᶠ d in atTop,
      SharpSphericalIsoperimetry
        (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
        (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
        (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
          (R.sample d))
        (PptFactorization.AppendixB.sphericalModelMeasure
          (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
          (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
          (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
            (R.sample d)))
        (upperConcreteRealDim R d) :=
  eventually_upper_hIso_concreteModel_of_fullSphericalIsoperimetry R
    (fullSphericalIsoperimetry_of_finRealSphereAutoHeightBandsAverageGainSup_capConeFlatteningMap
      hGeom)

/-- Mean-comparison input between the actual upper model and the deleted-column
lower background model.

This is not a definitional tautology: it compares two different centerings.  The
definition only hides the concrete `Fin d`, `Fin d`, `Fin (R.sample d)` indices
behind the canonical actual-model mean sequence. -/
def upperLowerConcreteMeanCompare
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) : Prop :=
  ∀ᶠ d in atTop,
    upperConcreteModelMeanSeq R k d ≤
      lowerConcreteDeletedBackgroundMean R k d

/-- The named mean-comparison input is exactly the raw concrete mean comparison
used by older endpoint wrappers. -/
theorem upperLowerConcreteMeanCompare_iff_raw
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (k : ℕ) :
    upperLowerConcreteMeanCompare R k ↔
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d ≤
          lowerConcreteDeletedBackgroundMean R k d := by
  rfl

/-- Turn the named mean-comparison input into the raw endpoint form. -/
theorem upperLowerConcreteMeanCompare.raw
    {R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {k : ℕ}
    (hCompare : upperLowerConcreteMeanCompare R k) :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d ≤
          lowerConcreteDeletedBackgroundMean R k d :=
  (upperLowerConcreteMeanCompare_iff_raw R k).1 hCompare

/-- Diagnostic: convergence of two scalar centerings to the same limit does not
by itself supply an eventual comparison in either direction.

This is why the upper/lower mean bridge cannot be closed merely by proving that
both centerings have the same Catalan limit.  A one-sided estimate on the
difference, or a sharper expansion with the correct sign, is needed. -/
theorem same_limit_does_not_force_eventual_le :
    ∃ u v : ℕ → ℝ,
      Tendsto u atTop (nhds 0) ∧
      Tendsto v atTop (nhds 0) ∧
      ¬ (∀ᶠ d in atTop, u d ≤ v d) := by
  refine
    ⟨(fun d : ℕ => if d = 0 then (1 : ℝ) else (1 : ℝ) / (d : ℝ)),
      (fun _d : ℕ => (0 : ℝ)), ?_, ?_, ?_⟩
  · have h_eventually :
        (fun d : ℕ => if d = 0 then (1 : ℝ) else (1 : ℝ) / (d : ℝ)) =ᶠ[atTop]
          (fun d : ℕ => (1 : ℝ) / (d : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with d hd
      simp [ne_of_gt hd]
    have h_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    exact Tendsto.congr' h_eventually.symm (by
      simpa [one_div] using (tendsto_inv_atTop_zero.comp h_atTop))
  · exact tendsto_const_nhds
  · intro h
    rcases eventually_atTop.1 h with ⟨N, hN⟩
    let n := max N 1
    have hNn : N ≤ n := le_max_left N 1
    have hnposNat : 0 < n :=
      lt_of_lt_of_le (by norm_num) (le_max_right N 1)
    have hle := hN n hNn
    have hdivpos : (0 : ℝ) < (1 : ℝ) / (n : ℝ) := by
      positivity
    simp [n, ne_of_gt hnposNat] at hle
    linarith

/-- Diagnostic: even an exact `O(1 / d)` absolute Catalan estimate around a
center `C` does not supply the one-sided upper margin needed by the signed
mean-comparison packet.

The constant sequence `u_d = C` has zero absolute error, but it cannot satisfy
`u_d <= C - E / d` for every requested `D` with some `E >= D`.  Thus an upper
mean theorem must include signed below-center information, not only convergence
or an absolute `D / d` Catalan error bound. -/
theorem exact_center_does_not_force_arbitrary_upper_margin (C : ℝ) :
    ∃ u : ℕ → ℝ,
      (∀ᶠ d : ℕ in atTop, |u d - C| ≤ (0 : ℝ) / (d : ℝ)) ∧
        ¬ (∀ D : ℝ, 0 ≤ D →
          ∃ E : ℝ, D ≤ E ∧
            ∀ᶠ d : ℕ in atTop, u d ≤ C - E / (d : ℝ)) := by
  refine ⟨(fun _d : ℕ => C), ?_, ?_⟩
  · exact Eventually.of_forall (by simp)
  · intro hmargin
    rcases hmargin 1 (by norm_num) with ⟨E, hE, hEventually⟩
    rcases eventually_atTop.1 hEventually with ⟨N, hN⟩
    let n := max N 1
    have hNn : N ≤ n := le_max_left N 1
    have hnposNat : 0 < n :=
      lt_of_lt_of_le (by norm_num) (le_max_right N 1)
    have hineq := hN n hNn
    have hEpos : 0 < E := by linarith
    have hdivpos : 0 < E / (n : ℝ) := by positivity
    have hnot : ¬ C ≤ C - E / (n : ℝ) := by linarith
    exact hnot hineq

/-- The preceding diagnostic specialized to the actual length-three Catalan
center.

Even exact zero error around `1 + 3 * R.lam⁻¹` does not imply the upper
signed-margin input used by the repaired mean comparison. -/
theorem exact_upper_catalan_center_does_not_force_upperMarginForAll
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∃ u : ℕ → ℝ,
      (∀ᶠ d : ℕ in atTop,
        |u d - (1 + 3 * R.lam⁻¹)| ≤ (0 : ℝ) / (d : ℝ)) ∧
        ¬ (∀ D : ℝ, 0 ≤ D →
          ∃ E : ℝ, D ≤ E ∧
            ∀ᶠ d : ℕ in atTop,
              u d ≤ (1 + 3 * R.lam⁻¹) - E / (d : ℝ)) := by
  simpa using
    exact_center_does_not_force_arbitrary_upper_margin
      (1 + 3 * R.lam⁻¹)

/-- The clean upper mean-margin frontier is genuinely signed information.

This restates the diagnostic in the language of the current clean endpoint:
even an exactly centered candidate sequence at the length-three Catalan value
does not force the margin family
`∀ D >= 0, upperConcreteModelMeanThreeCatalanUpperMarginFor R D`.  The missing
ingredient is not convergence to the Catalan center; it is a one-sided
`1 / d` gap below that center large enough to dominate the lower-side error. -/
theorem upper_clean_meanCatalanMargin_not_forced_by_exact_catalan_center_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    ∃ u : ℕ → ℝ,
      (∀ᶠ d : ℕ in atTop,
        |u d - (1 + 3 * R.lam⁻¹)| ≤ (0 : ℝ) / (d : ℝ)) ∧
        ¬ (∀ D : ℝ, 0 ≤ D →
          ∃ E : ℝ, D ≤ E ∧
            ∀ᶠ d : ℕ in atTop,
              u d ≤ (1 + 3 * R.lam⁻¹) - E / (d : ℝ)) :=
  exact_upper_catalan_center_does_not_force_upperMarginForAll R

/-- Signed length-three Catalan gap packet for the upper/lower mean comparison.

The lower deleted-column mean is within `D / d` of the Catalan center, while
the upper full-model mean lies at least `E / d` below that same center with
`D <= E`.  This is the signed information that a same-limit argument lacks. -/
def upperLowerConcreteMeanThreeCatalanSignedGap
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    Prop :=
  ∃ D E : ℝ,
    0 ≤ D ∧
      D ≤ E ∧
        (∀ᶠ d : ℕ in atTop,
          |lowerConcreteDeletedBackgroundMean R 3 d -
              (1 + 3 * R.lam⁻¹)| ≤ D / (d : ℝ)) ∧
          (∀ᶠ d : ℕ in atTop,
            upperConcreteModelMeanSeq R 3 d ≤
              (1 + 3 * R.lam⁻¹) - E / (d : ℝ))

/-- Upper full-model mean margin below the length-three Catalan center,
parameterized by the deleted-column error constant `D`.

This is the genuinely upper-model part of the signed mean comparison: once the
deleted-column side is known within `D / d`, the upper mean must sit below the
same Catalan center by at least `E / d` for some `E >= D`. -/
def upperConcreteModelMeanThreeCatalanUpperMarginFor
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (D : ℝ) : Prop :=
  ∃ E : ℝ,
    D ≤ E ∧
      ∀ᶠ d : ℕ in atTop,
        upperConcreteModelMeanSeq R 3 d ≤
          (1 + 3 * R.lam⁻¹) - E / (d : ℝ)

/-- Scaled upper Catalan deficit tending to infinity.

This is a compact asymptotic form of the upper mean-margin theorem: the
full-model length-three mean must sit below the Catalan center by more than any
prescribed multiple of `1 / d`. -/
def upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    Prop :=
  Tendsto
    (fun d : ℕ =>
      (d : ℝ) * ((1 + 3 * R.lam⁻¹) - upperConcreteModelMeanSeq R 3 d))
    atTop atTop

/-- A divergent scaled upper Catalan deficit supplies the upper mean-margin input.

In formulas, if
\[
  d\bigl((1+3\lambda^{-1})-m_{\mathrm{upper}}(d)\bigr)\to+\infty,
\]
then for every lower error constant `D >= 0` there is `E >= D` such that
eventually
\[
  m_{\mathrm{upper}}(d)\le (1+3\lambda^{-1})-E/d.
\]
This is scalar order bookkeeping; the theorem-strength work is proving the
scaled deficit. -/
theorem upperConcreteModelMeanThreeCatalanUpperMarginFor_of_scaledDeficitTendsToTop
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R) :
    ∀ D : ℝ, 0 ≤ D →
      upperConcreteModelMeanThreeCatalanUpperMarginFor R D := by
  intro D _hD
  refine ⟨D, le_rfl, ?_⟩
  have hEventually :
      ∀ᶠ d : ℕ in atTop,
        D ≤
          (d : ℝ) *
            ((1 + 3 * R.lam⁻¹) - upperConcreteModelMeanSeq R 3 d) := by
    exact hDeficit.eventually (eventually_ge_atTop D)
  filter_upwards [hEventually, eventually_gt_atTop 0] with d hd hpos
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast hpos
  have hd' :
      D ≤
        ((1 + 3 * R.lam⁻¹) - upperConcreteModelMeanSeq R 3 d) *
          (d : ℝ) := by
    simpa [mul_comm] using hd
  have hdiv :
      D / (d : ℝ) ≤
        (1 + 3 * R.lam⁻¹) - upperConcreteModelMeanSeq R 3 d := by
    exact (div_le_iff₀ hdpos).2 hd'
  linarith

/-- The deleted-column `D / d` Catalan estimate plus an upper-model signed
margin for the same `D` supply the signed Catalan gap packet. -/
theorem upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_upperMargin
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hLower :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hUpper :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D) :
    upperLowerConcreteMeanThreeCatalanSignedGap R := by
  rcases hLower with ⟨D, hD, hLowerD⟩
  rcases hUpper D hD with ⟨E, hDE, hUpperE⟩
  exact ⟨D, E, hD, hDE, hLowerD, hUpperE⟩

/-- The lower deleted-column `D / d` Catalan estimate plus a divergent scaled
upper Catalan deficit directly supply the signed gap packet. -/
theorem upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_scaledDeficit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hLower :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R) :
    upperLowerConcreteMeanThreeCatalanSignedGap R :=
  upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_upperMargin
    R hLower
    (upperConcreteModelMeanThreeCatalanUpperMarginFor_of_scaledDeficitTendsToTop
      R hDeficit)

/-- The signed Catalan gap packet supplies the scalar mean comparison. -/
theorem upperLowerConcreteMeanCompare_three_of_signedCatalanGap
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hGap : upperLowerConcreteMeanThreeCatalanSignedGap R) :
    upperLowerConcreteMeanCompare R 3 := by
  rcases hGap with ⟨D, E, hD, hDE, hLower, hUpper⟩
  filter_upwards [hLower, hUpper, eventually_gt_atTop 0] with d hLower_d hUpper_d hd
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hDEdiv : D / (d : ℝ) ≤ E / (d : ℝ) :=
    div_le_div_of_nonneg_right hDE hd_nonneg
  have hLower_ge :
      (1 + 3 * R.lam⁻¹) - D / (d : ℝ) ≤
        lowerConcreteDeletedBackgroundMean R 3 d := by
    have hneg :
        -(D / (d : ℝ)) ≤
          lowerConcreteDeletedBackgroundMean R 3 d - (1 + 3 * R.lam⁻¹) :=
      (abs_le.mp hLower_d).1
    linarith
  have hUpper_le_D :
      upperConcreteModelMeanSeq R 3 d ≤
        (1 + 3 * R.lam⁻¹) - D / (d : ℝ) := by
    linarith
  exact hUpper_le_D.trans hLower_ge

/-- The signed Catalan-gap packet contains the direct lower length-three
`D / d` Catalan estimate. -/
theorem lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_signedCatalanGap
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hGap : upperLowerConcreteMeanThreeCatalanSignedGap R) :
    lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R := by
  rcases hGap with ⟨D, _E, hD, _hDE, hLower, _hUpper⟩
  exact ⟨D, hD, hLower⟩

/-- The lower deleted-column `D / d` Catalan estimate plus a divergent scaled
upper Catalan deficit directly supply the scalar upper/lower mean comparison. -/
theorem upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_scaledDeficit
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hLower :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R) :
    upperLowerConcreteMeanCompare R 3 :=
  upperLowerConcreteMeanCompare_three_of_signedCatalanGap R
    (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_scaledDeficit
      R hLower hDeficit)

/-- The lower deleted-column `D / d` Catalan estimate plus a direct upper-model
Catalan margin supply the scalar upper/lower mean comparison. -/
theorem upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_upperMargin
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hLower :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hUpper :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D) :
    upperLowerConcreteMeanCompare R 3 :=
  upperLowerConcreteMeanCompare_three_of_signedCatalanGap R
    (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_upperMargin
      R hLower hUpper)

/-- The direct balanced-ratio length-three Catalan `D / d` estimate supplies
the older ratio-parametric Catalan-error package at the concrete balanced
ratio.

This is scalar adapter work: it changes the center from the literal
`1 + 3 * R.lam⁻¹` to the generic Catalan-limit notation at `k = 3`. -/
theorem lowerDeletedColumnBackgroundMomentCatalanErrorBound_of_threeCatalanDOverD_atBalancedRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R) :
    lowerDeletedColumnBackgroundMomentCatalanErrorBound R.sample R.lam 3 := by
  rcases hBound with ⟨D, hD, hEventually⟩
  refine ⟨D, hD, ?_⟩
  filter_upwards [hEventually] with d hd
  simpa [lowerDeletedBackgroundMeanCatalanLimit_three,
    lowerConcreteDeletedBackgroundMean,
    lowerDeletedColumnBackgroundMomentSequence] using hd

/-- The ratio-parametric direct length-three Catalan `D / d` estimate supplies
the older generic Catalan-error package at `k = 3`.

The only change is notation for the same Catalan center. -/
theorem lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_threeCatalanDOverD
    (sample : ℕ → ℕ)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio sample) :
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio sample 3 := by
  rcases hBound with ⟨D, hD, hBound⟩
  intro lam hratio
  refine ⟨D, hD, ?_⟩
  filter_upwards [hBound lam hratio] with d hd
  simpa [lowerDeletedBackgroundMeanCatalanLimit_three] using hd

/-- The direct balanced-ratio length-three Catalan `D / d` estimate supplies
the older ratio-parametric Catalan-error package at `k = 3`.

This uses uniqueness of the concrete balanced ratio to move from the
balanced-ratio statement to the ratio-parametric statement. -/
theorem lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_threeCatalanDOverD_atBalancedRatio
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (hBound :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R) :
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 :=
  lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_threeCatalanDOverD
    R.sample
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_atBalancedRatio
      R hBound)

/-- Target-probability comparison between the lower deleted-background target
and the upper actual-model target.

Plainly: the lower one-column event, centered at the deleted-background mean
and with threshold `lowerConcreteEps eps`, is eventually no larger in
probability than the actual upper event, centered at the upper model mean and
with threshold `eps`.  This is the probability bridge consumed by the upper
route. -/
def upperLowerConcreteTargetCompare
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : Prop :=
  ∀ᶠ d in atTop,
    lowerConcreteTargetProb R (lowerConcreteEps eps)
        (lowerConcreteDeletedBackgroundMean R k) k d ≤
      lowerConcreteTargetProb R (fun _d : ℕ => eps)
        (upperConcreteModelMeanSeq R k) k d

/-- The named target comparison is exactly the raw eventual probability
comparison used by the upper/lower bridge. -/
theorem upperLowerConcreteTargetCompare_iff_raw
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) :
    upperLowerConcreteTargetCompare R eps k ↔
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R k) k d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d := by
  rfl

/-- Turn the named target comparison into the raw endpoint form. -/
theorem upperLowerConcreteTargetCompare.raw
    {R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime}
    {eps : ℝ} {k : ℕ}
    (hCompare : upperLowerConcreteTargetCompare R eps k) :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R k) k d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d :=
  (upperLowerConcreteTargetCompare_iff_raw R eps k).1 hCompare

/-- Monotonicity bridge for the target comparison used by the upper/lower
column pipeline.

The event `eps <= F - mean` grows as the centering `mean` decreases.  Thus, if
the upper actual-model centering is eventually no larger than the
deleted-background centering, the deleted-background lower target is eventually
contained in the upper actual-model one-sided target. -/
theorem lowerConcreteTargetProb_deletedMean_le_upperModelMeanSeq_of_upperMeanSeq_le_deletedMean
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d) :
    ∀ᶠ d in atTop,
      lowerConcreteTargetProb R (lowerConcreteEps eps)
          (lowerConcreteDeletedBackgroundMean R k) k d ≤
        lowerConcreteTargetProb R (fun _d : ℕ => eps)
          (upperConcreteModelMeanSeq R k) k d := by
  filter_upwards [hMeanCompare, lower_concrete_eventually_two_le_sample R]
    with d hmean hs2
  have _hs : 0 < R.sample d := lt_of_lt_of_le (by norm_num) hs2
  letI : MeasureTheory.IsProbabilityMeasure
      (_root_.PptFactorization.AppendixB.sphericalModelMeasure
        (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))) :=
    _root_.PptFactorization.AppendixB.sphericalModelMeasure_isProbabilityMeasure
      (p := Fin d) (q := Fin d) (σ := Fin (R.sample d))
  unfold lowerConcreteTargetProb
  refine MeasureTheory.measureReal_mono ?_ (h₂ := (MeasureTheory.measure_lt_top _ _).ne)
  intro X hX
  change eps ≤ _ - upperConcreteModelMeanSeq R k d
  change lowerConcreteEps eps d ≤ _ - lowerConcreteDeletedBackgroundMean R k d at hX
  simp only [lowerConcreteEps_eq] at hX
  linarith

/-- The scalar centering comparison supplies the named target comparison by
event monotonicity. -/
theorem upperLowerConcreteTargetCompare_of_meanCompare
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ}
    (hMeanCompare : upperLowerConcreteMeanCompare R k) :
    upperLowerConcreteTargetCompare R eps k :=
  lowerConcreteTargetProb_deletedMean_le_upperModelMeanSeq_of_upperMeanSeq_le_deletedMean
    R (eps := eps) (k := k) hMeanCompare.raw

/-- Upper actual-model endpoint with the one-column lower pipeline wired in.

Compared with
`upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteColumnProb_exponentialDeviationSetBound_mixedRemainder`,
this wrapper supplies the concrete one-column inclusion, projective-cap
lower-bound package, and deleted-background half-mass package for the canonical
lower direction.  The remaining comparison input is the honest centering bridge
between the deleted-background lower target and the upper actual-model
one-sided target. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_targetCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hTraceStability : lowerConcreteCanonicalCapSpikeTraceStability k eps)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d)
    (hTargetCompare :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R k) k d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hUnitProfile :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k eps a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u :=
    lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
      hk1 hε hTraceStability
  have hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k eps :=
    lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
      (R := R) (k := k) (ε := eps) hk3 hε hMeanBound
  have hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (lowerConcreteMixedError R k eps) k eps :=
    lower_mixedLower_concreteChoices_of_localExpansionEnvelope
      (R := R) (k := k) (ε := eps) hMixedEnvelope
  have hColumnIncludedLower :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            lowerConcreteColumnProb R lowerConcreteCanonicalDirection
                (lowerConcreteM R) lowerConcreteTau
                (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
                k a slack d ≤
              lowerConcreteTargetProb R (lowerConcreteEps eps)
                (lowerConcreteDeletedBackgroundMean R k) k d :=
    lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
      (R := R) (k := k) (ε := eps) hk1 hε
      hUnitProfile hScaleBudget hMixedLower
  have hColumnIncluded :
      ∀ᶠ d in atTop,
        lowerConcreteColumnProb R lowerConcreteCanonicalDirection
            (lowerConcreteM R) lowerConcreteTau
            (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
            k (spikeRoot k eps + 1) 1 d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    filter_upwards
      [hColumnIncludedLower (spikeRoot k eps + 1) ha 1 hslack,
        hTargetCompare] with d hle hcmp
    exact hle.trans hcmp
  have hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (lowerConcreteCapProb R lowerConcreteCanonicalDirection
            (spikeRoot k eps + 1) 1 d)
          (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    exact
      lower_concrete_hCap_of_referenceCone_canonicalDirection
        (R := R) (k := k) (ε := eps)
        lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
        (spikeRoot k eps + 1) ha 1 hslack
  have hBackgroundHalf :
      ∀ᶠ d in atTop,
        (1 / 2 : ℝ) ≤
          lowerConcreteBackgroundProb R (lowerConcreteM R) lowerConcreteTau
            (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
            k (spikeRoot k eps + 1) 1 d := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    exact
      lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds_smallBudget
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := lowerConcreteMomentBound R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k) (ε := eps)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := lowerConcreteMomentBound R k)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMoment
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R))
        (lower_concrete_hMomentSmall R (k := k))
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold
        (spikeRoot k eps + 1) ha 1 hslack
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteColumnProb_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      lowerConcreteCanonicalDirection
      (M := lowerConcreteM R) (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (a := spikeRoot k eps + 1) (slack := 1)
      (by linarith) (by norm_num)
      hColumnIncluded hCap hBackgroundHalf hExp hUpperMixed

/-- Upper actual-model endpoint with the lower canonical column pipeline and
the target comparison reduced to an explicit centering inequality.

This is sharper than the `targetCompare` wrapper: the remaining bridge between
the lower target and the upper one-sided target is now the transparent eventual
mean comparison
`upperConcreteModelMeanSeq R k d <= lowerConcreteDeletedBackgroundMean R k d`.
-/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hTraceStability : lowerConcreteCanonicalCapSpikeTraceStability k eps)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_targetCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hTraceStability hMeanBound hMixedEnvelope hMoment
      (lowerConcreteTargetProb_deletedMean_le_upperModelMeanSeq_of_upperMeanSeq_le_deletedMean
        R (eps := eps) (k := k) hMeanCompare)
      hExp hUpperMixed

/-- Upper actual-model endpoint with the mean-side helper supplied by finite
convergence of the deleted-background mean.

This removes the theorem-facing helper
`lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded`; the remaining
mean-side input is the clearer finite-limit statement for
`lowerConcreteDeletedBackgroundMean`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanLimit_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hTraceStability : lowerConcreteCanonicalCapSpikeTraceStability k eps)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hTraceStability
      (lower_concrete_deletedBackgroundMean_positivePartEventuallyBounded_of_hasFiniteLimit
        (R := R) (k := k) hMeanLimit)
      hMixedEnvelope hMoment hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the pure-spike trace-stability package
reduced to the left-density diagonal-power frontier.

The cap-overlap algebra and scalar cap budget are supplied by existing local
lemmas; the remaining spike-side input is the smaller statement that the
rank-one partial-transpose trace power dominates the left-density diagonal
power. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_leftDensity_meanLimit_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hLeftDensity :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k)
    (hMeanLimit :
      ∃ m : ℝ,
        Tendsto (fun d : ℕ => lowerConcreteDeletedBackgroundMean R k d)
          atTop (nhds m))
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hTrace :
      lowerConcreteCanonicalCapSpikeTraceStability k eps :=
    lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower hk1 hε
      (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
        (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
          hLeftDensity))
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanLimit_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hTrace hMeanLimit hMixedEnvelope hMoment hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the deleted-background mean-limit input
reduced to the PT geodesic/noncrossing survivor frontier.

The Gaussian/radial Wick formula is supplied by its audited current predicate;
the remaining mean-side input is the survivor analysis that identifies the
Catalan contribution. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_leftDensity_ptSurvivors_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hLeftDensity :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_leftDensity_meanLimit_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup hLeftDensity
      (lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
        R k
        (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
          R.sample k)
        hSurvivors)
      hMixedEnvelope hMoment hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the left-density trace-power input closed
by the finite matrix core proofs.

Compared with the `leftDensity_ptSurvivors` wrapper, this no longer exposes the
pure-spike trace-power dominance package. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hMoment :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentBadSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              lowerConcreteMomentBound R k a slack d)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_leftDensity_ptSurvivors_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)
      hSurvivors hMixedEnvelope hMoment hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the deleted-background moment bad-set input
reduced to the named exponential deleted-background deviation frontier.

The strict bad-set formula is supplied by the closed-deviation adapter and the
scalar comparison `exp (-c d^2) <= exp (-d)` already proved in the lower
background-moment file. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hSurvivors hMixedEnvelope
      (lowerConcreteDeletedBackgroundMomentBadTailBound_of_deviationTailBound R k
        (lowerConcreteDeletedBackgroundMomentDeviationTailBound_of_exponentialDeviationTailBound
          R k hDeletedMomentExp))
      hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the deleted-column mean side reduced to
the explicit crossing/spherical Catalan `D / d` error estimate.

Compared with the `ptSurvivors` route, this exposes the paper-facing
finite-diagram estimate directly instead of the grouped survivor-analysis
predicate. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_leftDensity_meanLimit_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)
      (lowerConcreteDeletedBackgroundMeanHasFiniteLimit_of_deletedColumnMomentAsymptotic
        R k
        (lowerDeletedColumnBackgroundMomentHasCatalanLimit_of_fromRatio_errorBound
          R k hMeanError))
      hMixedEnvelope
      (lowerConcreteDeletedBackgroundMomentBadTailBound_of_deviationTailBound R k
        (lowerConcreteDeletedBackgroundMomentDeviationTailBound_of_exponentialDeviationTailBound
          R k hDeletedMomentExp))
      hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the lower deleted-background typicality
side reduced to the variance/Chebyshev moment tail and the mean side reduced
to the bounded-positive-part helper actually used by the scale-budget step.

The lower column pipeline only needs the background bad-event budget to be
eventually small.  Therefore the deleted-background half-mass step can use the
polynomial `C / d^2` tail coming from the two-trace Wick variance estimate,
instead of the stronger exponential deleted-background deviation estimate.

On the mean side, this theorem exposes the exact requirement used in the proof:
eventual boundedness of the positive part of the deleted-background mean.  More
structured Catalan or Wick-survivor routes can feed this helper through audited
adapters below. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k eps :=
    lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower hk1 hε
      (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
        (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
          (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))
  have hUnitProfile :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k eps a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u :=
    lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
      hk1 hε hTraceStability
  have hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k eps :=
    lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
      (R := R) (k := k) (ε := eps) hk3 hε hMeanBound
  have hMixedLower :
      lowerConcreteMixedLowerBound R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (lowerConcreteMixedError R k eps) k eps :=
    lower_mixedLower_concreteChoices_of_localExpansionEnvelope
      (R := R) (k := k) (ε := eps) hMixedEnvelope
  have hColumnIncludedLower :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            lowerConcreteColumnProb R lowerConcreteCanonicalDirection
                (lowerConcreteM R) lowerConcreteTau
                (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
                k a slack d ≤
              lowerConcreteTargetProb R (lowerConcreteEps eps)
                (lowerConcreteDeletedBackgroundMean R k) k d :=
    lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors
      (R := R) (k := k) (ε := eps) hk1 hε
      hUnitProfile hScaleBudget hMixedLower
  have hTargetCompare :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R k) k d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d :=
    lowerConcreteTargetProb_deletedMean_le_upperModelMeanSeq_of_upperMeanSeq_le_deletedMean
      R (eps := eps) (k := k) hMeanCompare
  have hColumnIncluded :
      ∀ᶠ d in atTop,
        lowerConcreteColumnProb R lowerConcreteCanonicalDirection
            (lowerConcreteM R) lowerConcreteTau
            (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
            k (spikeRoot k eps + 1) 1 d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    filter_upwards
      [hColumnIncludedLower (spikeRoot k eps + 1) ha 1 hslack,
        hTargetCompare] with d hle hcmp
    exact hle.trans hcmp
  have hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (lowerConcreteCapProb R lowerConcreteCanonicalDirection
            (spikeRoot k eps + 1) 1 d)
          (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    exact
      lower_concrete_hCap_of_referenceCone_canonicalDirection
        (R := R) (k := k) (ε := eps)
        lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
        (spikeRoot k eps + 1) ha 1 hslack
  have hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R k hVariance
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  have hBackgroundHalf :
      ∀ᶠ d in atTop,
        (1 / 2 : ℝ) ≤
          lowerConcreteBackgroundProb R (lowerConcreteM R) lowerConcreteTau
            (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
            k (spikeRoot k eps + 1) 1 d := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    exact
      lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds_smallBudget
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := lowerConcreteMomentPolynomialBound C R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k) (ε := eps)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := lowerConcreteMomentPolynomialBound C R k)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMomentBad
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R))
        (lower_concrete_polynomialMomentSmall C R k)
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold
        (spikeRoot k eps + 1) ha 1 hslack
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteColumnProb_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      lowerConcreteCanonicalDirection
      (M := lowerConcreteM R) (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (a := spikeRoot k eps + 1) (slack := 1)
      (by linarith) (by norm_num)
      hColumnIncluded hCap hBackgroundHalf hExp hUpperMixed

/-- Upper actual-model endpoint with the lower deleted-background typicality
side reduced to the variance/Chebyshev moment tail.

The lower column pipeline only needs the background bad-event budget to be
eventually small.  Therefore the deleted-background half-mass step can use the
polynomial `C / d^2` tail coming from the two-trace Wick variance estimate,
instead of the stronger exponential deleted-background deviation estimate.

The Catalan-error input is now only an adapter into the bounded-mean helper
used by the scale-budget step. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
        R k hMeanError)
      hMixedEnvelope hVariance hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the mean side rerouted through the PT
geodesic/noncrossing survivor core.

This keeps the variance/Chebyshev background-typicality route, but no longer
asks for the explicit Catalan `D / d` error estimate.  The upper scale-budget
step only needs eventual boundedness of the positive part of the
deleted-background mean, supplied here by the Gaussian/radial predicate and
survivor analysis. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    (hMixedEnvelope : lowerConcreteMixedLocalExpansionEnvelope R k eps)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
        R k
        (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
          R.sample k)
        hSurvivors)
      hMixedEnvelope hVariance hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the lower mixed input repaired to an
explicit error sequence.

The older endpoint above consumes
`lowerConcreteMixedLocalExpansionEnvelope R k eps`, whose definition hard-codes
the mixed error as `lowerConcreteMixedError`.  This wrapper follows the repaired
lower route instead: the mixed estimate is stated on the Frobenius sphere with
an explicit `errMix`, and the scalar requirement is the endpoint-relevant fact
that `errMix a slack d` is eventually smaller than any positive tolerance. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_targetCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hLowerMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k eps errMix)
    (hLowerMixedSmall :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hTargetCompare :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R k) k d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 3) hk3
  have hTraceStability :
      lowerConcreteCanonicalCapSpikeTraceStability k eps :=
    lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower hk1 hε
      (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
        (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
          (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)))
  have hUnitProfile :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k eps a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u :=
    lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
      hk1 hε hTraceStability
  have hScaleBudget :
      lowerConcreteBackgroundScaleBudgetOnBetaInterval R k eps :=
    lower_scaleBudget_concreteChoices_of_meanPositivePartEventuallyBounded
      (R := R) (k := k) (ε := eps) hk3 hε hMeanBound
  have hMixedLower :
      lowerConcreteMixedLowerBoundOnSphere R lowerConcreteCanonicalDirection
        (lowerConcreteM R) lowerConcreteTau
        (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        errMix k eps :=
    lower_mixedLowerOnSphere_concreteChoices_of_localExpansionEnvelopeOnSphereWithError
      (R := R) (k := k) (ε := eps) errMix hLowerMixedEnvelope
  have hColumnIncludedLower :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            lowerConcreteColumnProb R lowerConcreteCanonicalDirection
                (lowerConcreteM R) lowerConcreteTau
                (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
                k a slack d ≤
              lowerConcreteTargetProb R (lowerConcreteEps eps)
                (lowerConcreteDeletedBackgroundMean R k) k d :=
    lower_concrete_hColumnIncluded_of_closed_unitProfile_sphereBetaScaleBudget_sameBackgroundError_mixedLowerBound_sameMean_smallErrors_withMixedError
      (R := R) (k := k) (ε := eps) hk1 hε
      (errMix := errMix)
      hUnitProfile hScaleBudget hMixedLower hLowerMixedSmall
  have hColumnIncluded :
      ∀ᶠ d in atTop,
        lowerConcreteColumnProb R lowerConcreteCanonicalDirection
            (lowerConcreteM R) lowerConcreteTau
            (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
            k (spikeRoot k eps + 1) 1 d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R k) k d := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    filter_upwards
      [hColumnIncludedLower (spikeRoot k eps + 1) ha 1 hslack,
        hTargetCompare] with d hle hcmp
    exact hle.trans hcmp
  have hCap :
      ∀ᶠ d in atTop,
        ProjectiveCapProbabilityLowerBound
          (lowerConcreteCapProb R lowerConcreteCanonicalDirection
            (spikeRoot k eps + 1) 1 d)
          (lowerConcreteNcap d) (1 / (lowerConcreteNcap d : ℝ)) := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    exact
      lower_concrete_hCap_of_referenceCone_canonicalDirection
        (R := R) (k := k) (ε := eps)
        lower_referenceCone_BipIndex_Fin_eventually_concreteChoices
        (spikeRoot k eps + 1) ha 1 hslack
  have hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R k :=
    lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R k hVariance
  rcases
    lowerConcreteDeletedBackgroundMomentSecondMomentWickBadTailBound_of_deviationTailBound
      (R := R) (k := k) hMomentSecond with
    ⟨C, _hC, hMomentBad⟩
  have hBackgroundHalf :
      ∀ᶠ d in atTop,
        (1 / 2 : ℝ) ≤
          lowerConcreteBackgroundProb R (lowerConcreteM R) lowerConcreteTau
            (fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
            k (spikeRoot k eps + 1) 1 d := by
    have ha : spikeRoot k eps < spikeRoot k eps + 1 := by linarith
    have hslack : (0 : ℝ) < 1 := by norm_num
    exact
      lower_concrete_hBackgroundHalf_of_reduced_spherical_bad_bounds_smallBudget
        (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
        (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
        (bMoment := lowerConcreteMomentPolynomialBound C R k)
        (bSample := lowerConcreteSampleTailBound)
        (bGamma := lowerConcreteGammaTailBound)
        (k := k) (ε := eps)
        (lower_concrete_hReduced_of_moment_and_gaussian_operator_tails
          (R := R) (M := lowerConcreteM R) (τ := lowerConcreteTau)
          (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
          (bMoment := lowerConcreteMomentPolynomialBound C R k)
          (bSample := lowerConcreteSampleTailBound)
          (bGamma := lowerConcreteGammaTailBound)
          (k := k)
          hMomentBad
          (lower_concrete_hSampleTail_of_deletedColumn_operator_tails R)
          (lower_concrete_hGammaTail_of_deletedColumn_operator_tails R))
        (lower_concrete_polynomialMomentSmall C R k)
        lower_concrete_hSampleSmall_commonThreshold
        lower_concrete_hGammaSmall_commonThreshold
        (spikeRoot k eps + 1) ha 1 hslack
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerConcreteColumnProb_exponentialDeviationSetBound_mixedRemainder
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      lowerConcreteCanonicalDirection
      (M := lowerConcreteM R) (τ := lowerConcreteTau)
      (center := fun _a _slack d => lowerConcreteDeletedBackgroundMean R k d)
      (a := spikeRoot k eps + 1) (slack := 1)
      (by linarith) (by norm_num)
      hColumnIncluded hCap hBackgroundHalf hExp hUpperMixed

/-- Compatibility adapter: the centering inequality is one sufficient way to
obtain the actual target-probability comparison used by the repaired lower
mixed route.  The sharper theorem above takes that target comparison directly. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    (errMix : ℝ → ℝ → ℕ → ℝ)
    (hLowerMixedEnvelope :
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithError R k eps errMix)
    (hLowerMixedSmall :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ η : ℝ, 0 < η →
            ∀ᶠ d in atTop, errMix a slack d ≤ η)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_targetCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
    R hk3 hε hLemma43AutoHeightBandsDirectGainSup hMeanBound errMix
    hLowerMixedEnvelope hLowerMixedSmall hVariance
    (lowerConcreteTargetProb_deletedMean_le_upperModelMeanSeq_of_upperMeanSeq_le_deletedMean
      R (eps := eps) (k := k) hMeanCompare)
    hExp hUpperMixed

/-- Upper actual-model endpoint with the lower mixed input specialized to the
paper-facing partial-transpose mixed-error frontier.

The previous wrapper exposes a generic `errMix` and its eventual smallness.
Here `errMix` is chosen to be the corrected PT error
`lowerPartialTransposeMixedErrorD k (a + slack) M d`.  The envelope itself is
the named mixed supplier `mixed_noL_atLeastTwoQ_ge_neg_errMix`; the scalar
smallness is closed by `lowerPartialTransposeMixedErrorD_eventually_le`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptMixedError
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    {M : ℝ}
    (hLowerMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k :=
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
      R k hMeanError
  refine
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hMeanBound
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      ?_ ?_ hVariance hMeanCompare hExp hUpperMixed
  · exact
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        R k eps M hLowerMixed
  · intro a _ha slack _hslack η hη
    exact
      lowerPartialTransposeMixedErrorD_eventually_le
        (k := k) hk3 (a + slack) M η hη

/-- Upper actual-model endpoint with the lower mixed side stated at the
same-error mixed frontier.

The mixed input is no longer specialized to a fixed partial-transpose scalar
envelope.  It asks directly for the two facts used by the proof with the same
error sequence: the on-sphere local-expansion envelope and eventual smallness
of that error. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k :=
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
      R k hMeanError
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup hMeanBound errMix
      hLowerMixedFrontier.1 hLowerMixedFrontier.2 hVariance hMeanCompare hExp
      hUpperMixed

/-- Upper actual-model endpoint with the lower mixed input reduced to the
pointwise partial-transpose mixed-word estimate.

This is the sharper mixed frontier beneath
`mixed_noL_atLeastTwoQ_ge_neg_errMix`: the finite PT budget and scalar smallness
of `lowerPartialTransposeMixedErrorD` are internal, so the remaining mixed
input is the word-by-word on-sphere estimate with literal envelope
`lowerPartialTransposeMixedWordBoundD`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptPointwiseMixedWordBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 ≤ k := by omega
  have hLowerMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k eps M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := eps) (M := M) hk1 hε hM hLowerMixedWord
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptMixedError
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hMeanError hLowerMixed hVariance hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the lower mixed input reduced below the
pointwise PT word packet to the two direct scalar mixed-word cases.

This is intentionally not phrased using the known-false fixed-`M` scale
comparison packet.  The remaining lower mixed leaves are the direct estimates
for no-`L`, exactly-one-`Q` words and no-`L`, many-`Q` words. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk0 : 0 < k := by omega
  have hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := k) (ε := eps) (M := M)
      hk0 hε hM hOne hMany
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptPointwiseMixedWordBound
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hMeanError hM hLowerMixedWord hVariance hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the mean side routed through the PT
survivor core and the mixed side reduced to the two direct scalar PT cases.

This is the survivor-side companion of the Catalan-error scalar-case wrapper:
the explicit `D / d` Catalan error estimate is not consumed on this branch.
The only mean input is the geodesic/noncrossing survivor analysis, which feeds
the bounded-positive-part mean helper used by the scale-budget step. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk0 : 0 < k := by omega
  have hk1 : 1 ≤ k := by omega
  have hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k :=
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
      R k
      (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
        R.sample k)
      hSurvivors
  have hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps
        (fun a slack d => lowerPartialTransposeMixedWordBoundD k (a + slack) M d) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := k) (ε := eps) (M := M)
      hk0 hε hM hOne hMany
  have hLowerMixed :
      mixed_noL_atLeastTwoQ_ge_neg_errMix R k eps M :=
    mixed_noL_atLeastTwoQ_ge_neg_errMix_of_pointwiseWordBound
      (R := R) (k := k) (ε := eps) (M := M) hk1 hε hM hLowerMixedWord
  refine
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      hMeanBound
      (fun a slack d => lowerPartialTransposeMixedErrorD k (a + slack) M d)
      ?_ ?_ hVariance hMeanCompare hExp hUpperMixed
  · exact
      lowerConcreteMixedLocalExpansionEnvelopeOnSphereWithPTError_of_mixed_noL_atLeastTwoQ_ge_neg_errMix
        R k eps M hLowerMixed
  · intro a _ha slack _hslack η hη
    exact
      lowerPartialTransposeMixedErrorD_eventually_le
        (k := k) hk3 (a + slack) M η hη

/-- Upper actual-model endpoint with the geometric input stated in the
average-form Lemma 4.3 packet.

The direct `sSup` rectangular-block supplier is built internally by the audited
geometric adapter
`lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hDirect :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)) :=
    PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hDirect
      hMeanError hM hOne hMany hVariance hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with average-form Lemma 4.3 geometry, the mean
side routed through PT survivors, and the mixed side reduced to the two direct
scalar PT cases.

This is the non-Catalan-error companion of the preceding wrapper.  The
geometric adapter from average gain to direct `sSup` gain is internal, and the
mean-side visible input is the survivor analysis rather than the explicit
finite-diagram Catalan error estimate. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hDirect :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)) :=
    PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hDirect
      hSurvivors hM hOne hMany hVariance hMeanCompare hExp hUpperMixed

/-- Upper actual-model endpoint with the upper mixed-remainder input split into
its two deterministic constituents: a model-level mixed-word bound and the
scalar limit saying the resulting finite envelope vanishes.

This does not prove the word estimates themselves.  It makes the remaining
upper mixed challenge explicit, so the broad `UpperConcreteModelMixedRemainderBound`
is no longer a theorem-facing black box on this route. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBounds_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit k
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 ≤ k := by omega
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hLemma43AutoHeightBands
      hSurvivors hM hOne hMany hVariance hMeanCompare hExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
        (R := R) (eps := eps) (k := k)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        hk1 hUpperWord hUpperTerm)

/-- Upper actual-model endpoint with the upper mixed scalar limit split into
the three branchwise limits: exactly one linear defect, exactly one quadratic
defect, and the remaining multi-defect words.

This is a scalar-frontier sharpening of the preceding wrapper.  The model-level
word estimate remains visible, but the term-limit input is no longer a single
black-box limit over all mixed words. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 ≤ k := by omega
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hLemma43AutoHeightBands
      hSurvivors hM hOne hMany hVariance hMeanCompare hExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
        (R := R) (eps := eps) (k := k)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        hk1 hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
        hUpperMultiTerm)

/-- Named-geometry version of the general casewise upper mixed endpoint.

The geometric assumption is the same average-form auto-height-band packet used
elsewhere; this wrapper prevents the raw quantifier block from becoming a
separate-looking theorem-facing input. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hSurvivors hM hOne hMany hVariance hMeanCompare hExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-geometry and named-mean version of the general casewise upper mixed
endpoint.

This wrapper leaves both adapter-level inputs at their readable names.  The
remaining visible assumptions are the actual analytic suppliers: lower survivor
analysis, lower variance, upper concentration, upper word bounds, and the three
upper mixed scalar branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    R hk3 hε hLemma43AutoHeightBands hSurvivors hM hOne hMany hVariance
    hMeanCompare hExp hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
    hUpperMultiTerm

/-- Upper actual-model endpoint with the lower mixed side stated at the honest
mixed-error frontier.

This is the repaired companion to the fixed-`M` PT scalar-case route below.
The lower mixed input is no longer a literal fixed-envelope packet; it is the
same-error pair
`lowerConcreteMixedErrorFrontier R k eps errMix`, namely a sphere-supported
mixed local-expansion envelope and eventual smallness for that very error
sequence.  The upper mixed side remains split into the model word estimate and
the three scalar branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hDirect :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)) :=
    PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  have hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k :=
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_gaussianRadialFormulaAndGeodesicSurvivorsFromRatio
      R k
      (lowerDeletedColumnPTGaussianRadialFormula_fromRatio_currentPredicate
        R.sample k)
      hSurvivors
  have hk1 : 1 ≤ k := by omega
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R hk3 hε hDirect hMeanBound errMix
      hLowerMixedFrontier.1 hLowerMixedFrontier.2
      hVariance hMeanCompare hExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
        (R := R) (eps := eps) (k := k)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        hk1 hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
        hUpperMultiTerm)

/-- Named-geometry and named-mean version of the lower mixed-error-frontier
endpoint.

This is the same repaired lower mixed route as above, but with the two
adapter-level inputs kept at readable names: the finite-sphere geometry packet
and the upper/lower mean comparison. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hSurvivors hLowerMixedFrontier hVariance hMeanCompare hExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model survivor endpoint with the deleted-background
variance/Chebyshev rate supplied from an exponential deviation tail.

The lower mixed side remains the repaired same-error frontier
`lowerConcreteMixedErrorFrontier R k eps errMix`.  This wrapper only removes
the polynomial deleted-background moment-tail bookkeeping from the public
signature: an exponential deleted-background deviation estimate is converted
internally to the paper-facing `C / d^2` Chebyshev budget. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    R hk3 hε hLemma43AutoHeightBands hSurvivors hLowerMixedFrontier
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
      R k hDeletedMomentExp)
    hMeanCompare hExp hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
    hUpperMultiTerm

/-- Named-adapter version of the survivor endpoint whose deleted-background
variance input is supplied by an exponential deviation estimate.

Compared with the named lower mixed-error frontier route, this wrapper also
replaces the variance packet by the stronger deleted-background exponential tail
that already implies it. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hSurvivors hLowerMixedFrontier hDeletedMomentExp hMeanCompare hExp
    hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model survivor endpoint with the lower mixed frontier unfolded
to word-by-word bounds, a finite scalar budget, and eventual smallness.

This wrapper keeps the exponential deleted-background moment tail from the
preceding endpoint, but removes the packaged
`lowerConcreteMixedErrorFrontier R k eps errMix` from the public signature.  The
mixed lower input is now exactly the deterministic pointwise word estimate, the
finite mixed-word budget for the chosen error sequence, and the `o(1)` smallness
of that same sequence. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedWordBoundsBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedBudget :
      lowerConcreteMixedWordBudgetWithError R k eps bound errMix)
    (hLowerMixedSmall :
      lowerConcreteMixedErrorEventuallySmall k eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hk1 : 1 ≤ k := by omega
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontier
      R hk3 hε hLemma43AutoHeightBands hSurvivors
      (lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
        (R := R) (k := k) (ε := eps) hk1 bound errMix
        hLowerMixedWord hLowerMixedBudget hLowerMixedSmall)
      hDeletedMomentExp hMeanCompare hExp hUpperWord hUpperOneLinearTerm
      hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the lower mixed word-budget route.

This keeps the geometry and mean comparison at their named interface level
while still exposing the actual lower mixed frontier pieces: a pointwise
mixed-word bound, a finite scalar budget, and eventual smallness of the same
error sequence. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedWordBoundsBudget
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedBudget :
      lowerConcreteMixedWordBudgetWithError R k eps bound errMix)
    (hLowerMixedSmall :
      lowerConcreteMixedErrorEventuallySmall k eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedWordBoundsBudget
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hSurvivors hLowerMixedWord hLowerMixedBudget hLowerMixedSmall
    hDeletedMomentExp hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model survivor endpoint with the lower mixed budget closed by
choosing the exact finite filtered mixed-word sum as the error sequence.

Compared with the `lowerMixedWordBoundsBudget` endpoint, this wrapper removes
the separate scalar budget hypothesis.  The remaining lower mixed inputs are
the pointwise mixed-word estimate and eventual smallness of the exact finite
sum of the selected word bounds. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedWordBoundsBudget
    R hk3 hε hLemma43AutoHeightBands hSurvivors hLowerMixedWord
    (lowerConcreteMixedWordBudgetWithExactSum R k eps bound)
    hLowerMixedExactSumSmall hDeletedMomentExp hMeanCompare hExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the exact finite mixed-word sum route.

This wrapper removes the raw geometry block and raw eventual mean comparison
from the exact-sum endpoint.  The lower mixed frontier is now represented by
the pointwise word estimate plus smallness of the exact finite filtered sum. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hSurvivors hLowerMixedWord hLowerMixedExactSumSmall hDeletedMomentExp
    hMeanCompare hExp hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
    hUpperMultiTerm

/-- Upper actual-model endpoint with the mean side stated at exactly the
bounded-positive-part input used by the one-column scale budget.

This is the article-facing companion to the survivor endpoint above.  The
upper argument itself only consumes eventual boundedness of the positive part
of the deleted-background mean; PT survivor combinatorics, Catalan-limit
estimates, or explicit diagram bounds are separate suppliers for that mean
input.  The lower mixed side keeps the repaired exact finite mixed-word sum. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hDirect :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)) :=
    PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  have hk1 : 1 ≤ k := by omega
  let errMix : ℝ → ℝ → ℕ → ℝ :=
    fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)
  have hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix :=
    lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
      (R := R) (k := k) (ε := eps) hk1 bound errMix
      hLowerMixedWord
      (lowerConcreteMixedWordBudgetWithExactSum R k eps bound)
      hLowerMixedExactSumSmall
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R hk3 hε hDirect hMeanBound errMix
      hLowerMixedFrontier.1 hLowerMixedFrontier.2
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
        R k hDeletedMomentExp)
      hMeanCompare hExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
        (R := R) (eps := eps) (k := k)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        hk1 hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
        hUpperMultiTerm)

/-- Upper actual-model endpoint with the mean-side boundedness supplied from
the explicit deleted-column Catalan `D / d` error estimate.

This keeps the latest exact lower mixed-word-sum route and exposes the concrete
moment theorem that supplies the bounded-positive-part mean input. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε hLemma43AutoHeightBands
    (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
      R k hMeanError)
    hLowerMixedWord hLowerMixedExactSumSmall hDeletedMomentExp hMeanCompare hExp
    hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the mean-bounded exact-sum endpoint.

The positive-part mean boundedness remains theorem-facing, but the geometry and
mean comparison are stated through their named interfaces. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R k)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hMeanBound hLowerMixedWord hLowerMixedExactSumSmall hDeletedMomentExp
    hMeanCompare hExp hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
    hUpperMultiTerm

/-- Upper actual-model endpoint with the deleted-column Catalan side exposed as
the finite-diagram crossing/spherical-correction estimate.

The adapter from this finite-diagram statement to the `D / d` Catalan-error
packet is already checked in the lower mean-limit file. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
      R hk3 hε hLemma43AutoHeightBands
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hExplicitCatalan)
      hLowerMixedWord hLowerMixedExactSumSmall hDeletedMomentExp hMeanCompare hExp
      hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the explicit Catalan diagram endpoint.

The finite-diagram Catalan estimate remains the theorem-facing mean supplier;
geometry and mean comparison are stated through their named interfaces. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hLowerMixedWord hLowerMixedExactSumSmall
    hDeletedMomentExp hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the lower deleted-background typicality
side kept at the variance/Chebyshev frontier.

Compared with the exponential-tail endpoint above, this wrapper exposes the
weaker background input actually consumed by the one-column half-mass step:
`deletedColumnSphericalMoment_variance_le_const_div_d4 R k`.  The mean side is
still the explicit finite-diagram Catalan estimate, and the lower mixed side is
still the exact finite filtered mixed-word sum. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  have hDirect :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)) :=
    PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      hLemma43AutoHeightBands
  have hk1 : 1 ≤ k := by omega
  let errMix : ℝ → ℝ → ℕ → ℝ :=
    fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)
  have hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R k eps errMix :=
    lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
      (R := R) (k := k) (ε := eps) hk1 bound errMix
      hLowerMixedWord
      (lowerConcreteMixedWordBudgetWithExactSum R k eps bound)
      hLowerMixedExactSumSmall
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R hk3 hε hDirect
      (lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_explicitCatalanDiagramBoundFromRatio
        R k m Wcard Cmodel hExplicitCatalan)
      errMix hLowerMixedFrontier.1 hLowerMixedFrontier.2
      hVariance hMeanCompare hExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
        (R := R) (eps := eps) (k := k)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        hk1 hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
        hUpperMultiTerm)

/-- Named-adapter version of the explicit Catalan plus variance-stack endpoint.

The finite Catalan estimate and the variance/Chebyshev background control
remain theorem-facing.  The geometry and centering bridge are stated through
their named interfaces. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedExactSumSmall :
      lowerConcreteMixedErrorEventuallySmall k eps
        (fun a slack d => localMixedWordFilteredSum (k := k) (bound a slack d)))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hLowerMixedWord hLowerMixedExactSumSmall
    hVariance (upperLowerConcreteMeanCompare.raw hMeanCompare) hExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the exact lower mixed finite-sum
smallness supplied from termwise convergence of the mixed word bounds.

The wrapper removes the opaque scalar smallness input
`lowerConcreteMixedErrorEventuallySmall ... localMixedWordFilteredSum` from the
public signature.  What remains is the termwise `o(1)` statement for each
mixed local-expansion word; the passage from those finitely many limits to the
filtered-sum smallness is pure finite-sum topology. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedTermwiseSmall
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound)
    (hLowerMixedTermwise :
      ∀ a : ℝ, spikeRoot k eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ w : Fin k → LocalExpansionLetter,
            localWordIsMixed w →
              Tendsto (fun d : ℕ => bound a slack d w) atTop (nhds 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hLowerMixedWord
    (lowerConcreteMixedErrorEventuallySmall_of_filteredSum_termwise_tendsto
      hLowerMixedTermwise)
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the literal PT lower mixed envelope.

For the PT envelope `lowerPartialTransposeMixedWordBoundD`, the termwise
`o(1)` hypothesis required by the previous wrapper is supplied internally from
`lowerPartialTransposeMixedWordBoundD_termwise_tendsto`.  The remaining lower
mixed input is the sphere-supported pointwise PT word estimate itself. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTWordBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD k (a + slack) M d))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedTermwiseSmall
    R hk3 hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hLowerMixedWord
    (lowerPartialTransposeMixedWordBoundD_termwise_tendsto
      (k := k) (ε := eps) (M := M) hk3 hε hM)
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the PT-envelope lower mixed route.

The lower PT pointwise word estimate remains visible.  The termwise-to-finite
sum passage is supplied internally, and geometry plus mean comparison are
stated through their named interfaces. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTWordBound
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD k (a + slack) M d))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hLowerMixedWord
    (lowerConcreteMixedErrorEventuallySmall_of_filteredSum_termwise_tendsto
      (lowerPartialTransposeMixedWordBoundD_termwise_tendsto
        (k := k) (ε := eps) (M := M) hk3 hε hM))
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the lower PT pointwise mixed-word input
reduced to the two direct scalar cases.

The wrapper supplies the sphere-supported pointwise PT word estimate from the
finite word split: words containing `L` vanish, exactly-one-`Q` words use
`hOne`, and many-`Q` words use `hMany`.  The literal PT termwise smallness and
finite-sum bookkeeping remain internal through the `lowerPTWordBound` endpoint.
-/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTWordBound
    R hk3 hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hM
    (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := k) (ε := eps) (M := M)
      (by omega) hε hM hOne hMany)
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the PT direct scalar lower mixed route.

The public lower mixed inputs are the one-`Q` and many-`Q` scalar estimates.
The pointwise PT word bound, finite-sum passage, geometry adapter, and mean
comparison adapter are supplied internally. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTWordBound
    R hk3 hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan hM
    (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := k) (ε := eps) (M := M)
      (by omega) hε hM hOne hMany)
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the PT direct scalar lower mixed leaves and
the deleted-background variance budget supplied from an exponential moment tail.

This combines the PT direct-scalar route with the sharper deleted-background
concentration input used by the exact mixed-word-sum endpoint: the public
signature no longer exposes the polynomial variance/Chebyshev conversion, which
is supplied internally from
`lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerMixedExactWordSumSmall
    R hk3 hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := k) (ε := eps) (M := M)
      (by omega) hε hM hOne hMany)
    (lowerConcreteMixedErrorEventuallySmall_of_filteredSum_termwise_tendsto
      (lowerPartialTransposeMixedWordBoundD_termwise_tendsto
        (k := k) (ε := eps) (M := M) hk3 hε hM))
    hDeletedMomentExp hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the deleted-moment-exponential PT direct-scalar
route.

This removes the raw geometry formula and raw eventual mean comparison from
the theorem-facing interface.  The finite Catalan estimate, lower PT direct
scalar estimates, deleted-background exponential tail, upper concentration,
and upper mixed word/limit packet remain visible. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
    R hk3 hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hM hOne hMany hDeletedMomentExp
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the lower PT direct scalar mixed-word
leaves reduced to their exact scale comparisons.

Compared with the `ptDirectScalarCases` endpoint, this wrapper no longer asks
for the one-`Q` and many-`Q` direct trace estimates.  Those are supplied by the
proved local trace estimates
`lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison` and
`lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison`.  The
fixed-envelope condition `0 ≤ M` is derived from the many-`Q` scale comparison
itself, so the live mixed lower inputs are the two scalar comparisons. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptScaleComparisons
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ}
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k eps M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    R hk3 hε hLemma43AutoHeightBands hSurvivors
    (lowerConcretePTMixedWordManyQScaleComparison_nonneg_M
      (R := R) (k := k) (ε := eps) (M := M) hk3 hε hManyScale)
    (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
      (R := R) (k := k) (ε := eps) (M := M) hk3 hε hOneScale)
    (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
      (R := R) (k := k) (ε := eps) (M := M) hk3 hε hManyScale)
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-adapter version of the PT scale-comparison route.

The lower mixed leaves are the one-`Q` and many-`Q` scale comparisons.  The
nonnegativity of the PT envelope, the direct scalar estimates, geometry, and
mean comparison are supplied internally. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptScaleComparisons
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSurvivors :
      lowerDeletedColumnPTGeodesicSurvivorAnalysis_fromRatio R.sample k)
    {M : ℝ}
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R k eps M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_ptSurvivors_varianceStack_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_ptDirectScalarCases
    R hk3 hε hLemma43AutoHeightBands hSurvivors
    (lowerConcretePTMixedWordManyQScaleComparison_nonneg_M
      (R := R) (k := k) (ε := eps) (M := M) hk3 hε hManyScale)
    (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
      (R := R) (k := k) (ε := eps) (M := M) hk3 hε hOneScale)
    (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
      (R := R) (k := k) (ε := eps) (M := M) hk3 hε hManyScale)
    hVariance hMeanCompare hExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Upper actual-model endpoint with the deleted-column Catalan side exposed
as the explicit finite-diagram `D / d` estimate.

This replaces the broader existential Catalan-error packet by the sharper
crossing-pairing plus spherical-correction estimate.  The adapter to the
older `lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio` input is
pure scalar packaging. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                      tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                      avg ≤
                                        sSup
                                          (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                            n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    (hUpperMixed : UpperConcreteModelMixedRemainderBound R eps k) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hLemma43AutoHeightBands
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hExplicitCatalan)
      hM hOne hMany hVariance hMeanCompare hExp hUpperMixed

/-- Sharp upper actual-model endpoint with direct Lemma 4.3 geometry.

Compared with
`upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases`,
this wrapper replaces the average-form auto-height-band geometry by the direct
block-to-`sSup` Lemma 4.3 package.  All non-geometric leaves remain the same:
explicit deleted-column Catalan diagram bound, PT direct scalar cases, deleted
background exponential moment tail, upper/deleted mean comparison, upper
exponential deviation, actual-model upper mixed-word bound, and the three upper
scalar mixed branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps M)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel hExplicitCatalan)
      hM hOne hMany
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
        R k hDeletedMomentExp)
      hMeanCompare hExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
        R (by omega) hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
        hUpperMultiTerm)

/-- Sharp upper actual-model endpoint with the PT scalar constant normalized.

Compared with
`upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases`,
this wrapper removes the standalone side condition `0 <= M` from the theorem
frontier.  The two genuine PT scalar estimates are asked at the nonnegative
constant `max M 0`, so the lower mixed adapter receives nonnegativity by
bookkeeping. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan
      (M := max M 0) (le_max_right M 0)
      hOne hMany hDeletedMomentExp hMeanCompare hExp
      hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-average-geometry version of the normalized-`M` PT direct-scalar
endpoint.

The direct height-band geometry and raw eventual mean comparison are supplied
internally from the named average geometry packet and named centering
comparison.  The normalized PT scalar estimates remain theorem-facing at
`max M 0`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompareNamed_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hExp : UpperConcreteModelMomentExponentialDeviationSetBound R c k)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    R hk3 hε
    (PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
    m Wcard Cmodel hExplicitCatalan M hOne hMany hDeletedMomentExp
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Sharp upper actual-model endpoint with the upper exponential-deviation
input unfolded.

Compared with the normalized-`M` wrapper, this endpoint no longer exposes the
named package `UpperConcreteModelMomentExponentialDeviationSetBound`.  Instead
it asks directly for a positive exponent `c` and the actual full-model
closed-deviation tail bounded by `exp (-c d^2)`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_upperExponentialTail_meanCompare_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {c : ℝ}
    (hc : 0 < c)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            upperConcreteModelExponentialMomentEnvelope c slack d)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_meanCompare_exponentialDeviationSetBound_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan M hOne hMany hDeletedMomentExp
      hMeanCompare ⟨hc, hUpperExpTail⟩ hUpperWord hUpperOneLinearTerm
      hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-average-geometry version of the normalized-`M` endpoint with the
upper exponential tail unfolded.

The upper full-model tail remains theorem-facing as the explicit positive
exponent plus eventual deviation estimate.  Geometry and centering are supplied
from the named average-geometry and mean-comparison packets. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_upperExponentialTail_meanCompareNamed_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R k)
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {c : ℝ}
    (hc : 0 < c)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            upperConcreteModelExponentialMomentEnvelope c slack d)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_upperExponentialTail_meanCompare_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    R hk3 hε
    (PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
    m Wcard Cmodel hExplicitCatalan M hOne hMany hDeletedMomentExp
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hc hUpperExpTail
    hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Sharp upper actual-model endpoint with both exponential-deviation packages
unfolded.

Compared with the upper-exponential-tail wrapper, this endpoint also no longer
exposes the named lower deleted-background package
`lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound`.  Instead it
asks directly for a positive lower exponent and the deleted-column closed
deviation tail bounded by `exp (-cLower d^2)`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompare_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    {cLower : ℝ}
    (hcLower : 0 < cLower)
    (hLowerExpTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              Real.exp (-(cLower * (d : ℝ) ^ 2)))
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_upperExponentialTail_meanCompare_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan M hOne hMany
      ⟨cLower, hcLower, hLowerExpTail⟩ hMeanCompare
      hcUpper hUpperExpTail hUpperWord hUpperOneLinearTerm
      hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-average-geometry version of the normalized-`M` endpoint with both
exponential tails unfolded.

Both lower deleted-background and upper full-model exponential tails remain
theorem-facing as explicit estimates.  Geometry and centering are supplied from
their named packets. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompareNamed_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    {cLower : ℝ}
    (hcLower : 0 < cLower)
    (hLowerExpTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              Real.exp (-(cLower * (d : ℝ) ^ 2)))
    (hMeanCompare : upperLowerConcreteMeanCompare R k)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompare_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    R hk3 hε
    (PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
    m Wcard Cmodel hExplicitCatalan M hOne hMany
    hcLower hLowerExpTail (upperLowerConcreteMeanCompare.raw hMeanCompare)
    hcUpper hUpperExpTail hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Sharp upper actual-model endpoint with the upper mixed-word package
unfolded.

Compared with the preceding wrapper, this endpoint no longer exposes the named
package `UpperConcreteModelMixedWordBound`.  Instead it asks directly for the
eventual deterministic word-by-word estimate on the actual upper model. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompare_upperMixedWordExplicit_caseTermLimits_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    {cLower : ℝ}
    (hcLower : 0 < cLower)
    (hLowerExpTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              Real.exp (-(cLower * (d : ℝ) ^ 2)))
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) k Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit k Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit k Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit k Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompare_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_normalizedM
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan M hOne hMany
      hcLower hLowerExpTail hMeanCompare hcUpper hUpperExpTail
      hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Sharp upper actual-model endpoint with the scalar mixed-branch packages
unfolded.

Compared with the preceding wrapper, this endpoint no longer exposes the named
scalar branch packages `UpperConcreteOneLinearMixedTermLimit`,
`UpperConcreteOneQuadraticMixedTermLimit`, and
`UpperConcreteMultiDefectMixedTermLimit`.  Instead it asks directly for the
three `Tendsto` statements used by those packages. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    {cLower : ℝ}
    (hcLower : 0 < cLower)
    (hLowerExpTail :
      ∀ a : ℝ, ∀ slack : ℝ,
        ∀ᶠ d in atTop,
          ∀ hs : 0 < R.sample d,
            (_root_.PptFactorization.AppendixB.sphericalModelMeasure
              (p := Fin d) (q := Fin d)
              (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))).real
              (backgroundMomentDeviationSet
                (p := Fin d) (q := Fin d)
                (σ := DeletedColumn (⟨0, hs⟩ : Fin (R.sample d)))
                (lowerConcreteN d) (lowerConcreteTau a slack d)
                (lowerConcreteDeletedBackgroundMean R k d) k) ≤
              Real.exp (-(cLower * (d : ℝ) ^ 2)))
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteModelMeanSeq R k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) k Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hUpperOneLinearTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (k - 1) *
              Abound slack d ^ (k - 1) * L1bound slack d)
          atTop (nhds 0))
    (hUpperOneQuadraticTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (k - 1) *
              Abound slack d ^ (k - 1) * Q1bound slack d)
          atTop (nhds 0))
    (hUpperMultiTerm :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            Tendsto
              (fun d =>
                upperConcreteN d ^ (k - 1) *
                  Abound slack d ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  L2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  Q2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.Q w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_lowerDeletedExponentialTail_upperExponentialTail_meanCompare_upperMixedWordExplicit_caseTermLimits_lowerPTDirectScalarCases_normalizedM
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan M hOne hMany
      hcLower hLowerExpTail hMeanCompare hcUpper hUpperExpTail
      (by
        intro slack hslack
        filter_upwards [hUpperWord slack hslack] with d hWord_d
        intro X Y hY hdist w hw
        exact hWord_d (by simpa [backgroundTypicalSet] using hY) hdist w hw)
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Sharp upper actual-model endpoint with the ratio-parametric Catalan diagram
input unfolded and the deleted-background input kept at the variance frontier.

Compared with the preceding wrapper, this endpoint no longer exposes the named
package `lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio`.
Instead it asks directly for the finite-diagram estimate at every limiting
deleted-column aspect ratio `lam`.

It also avoids routing the deleted-background side through an exponential
moment tail.  The lower one-column half-mass step consumes only the
variance/Chebyshev predicate
`deletedColumnSphericalMoment_variance_le_const_div_d4 R k`, so that is the
theorem-facing input here. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanRatio_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk3 : 3 ≤ k) (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      ∀ lam : ℝ,
        Tendsto
          (fun d : ℕ => ((R.sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
          atTop (nhds lam) →
        lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound
          R.sample lam k m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R k eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R k eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R k)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            k d ≤
          lowerConcreteDeletedBackgroundMean R k d)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d)
              k) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) k Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                k d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed k d)
                (upperSlackRadius (spikeRoot k eps) R.lam slack) →
            ∀ w : Fin k → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) k w)
    (hUpperOneLinearTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (k - 1) *
              Abound slack d ^ (k - 1) * L1bound slack d)
          atTop (nhds 0))
    (hUpperOneQuadraticTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (k - 1) *
              Abound slack d ^ (k - 1) * Q1bound slack d)
          atTop (nhds 0))
    (hUpperMultiTerm :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin k → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            Tendsto
              (fun d =>
                upperConcreteN d ^ (k - 1) *
                  Abound slack d ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  L2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  Q2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.Q w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps k d) / spikeSpeed k d ≤
          -spikeRate k R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R hk3 hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample k m Wcard Cmodel
        (by
          intro lam hratio
          exact hExplicitCatalan lam hratio))
      (M := max M 0) (le_max_right M 0) hOne hMany hVariance
      (by simpa [upperConcreteModelMeanSeq] using hMeanCompare)
      ⟨hcUpper, by
        intro slack hslack
        filter_upwards [hUpperExpTail slack hslack] with d hTail_d
        simpa [upperConcreteModelExponentialMomentEnvelope] using hTail_d⟩
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
        (R := R) (eps := eps) (k := k)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by omega)
        (by
          intro slack hslack
          filter_upwards [hUpperWord slack hslack] with d hWord_d
          intro X Y hY hdist w hw
          exact hWord_d (by simpa [backgroundTypicalSet] using hY) hdist w hw)
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three specialization of the current sharp upper actual-model
endpoint.

This wrapper removes the ambient moment-length parameter from the theorem
frontier.  All remaining inputs are now stated directly at the manuscript
length `k = 3`: the direct Lemma 4.3 geometry, the explicit deleted-column
Catalan diagram estimate, the two PT direct scalar estimates, the
deleted-column variance/Chebyshev predicate, the upper/deleted mean comparison,
the upper full-model exponential tail, the actual-model upper mixed-word
estimate, and the three scalar upper mixed branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanRatio_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      ∀ lam : ℝ,
        Tendsto
          (fun d : ℕ => ((R.sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
          atTop (nhds lam) →
        lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound
          R.sample lam 3 m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) 3 Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed 3 d)
                (upperSlackRadius (spikeRoot 3 eps) R.lam slack) →
            ∀ w : Fin 3 → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) 3 w)
    (hUpperOneLinearTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * L1bound slack d)
          atTop (nhds 0))
    (hUpperOneQuadraticTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * Q1bound slack d)
          atTop (nhds 0))
    (hUpperMultiTerm :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin 3 → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            Tendsto
              (fun d =>
                upperConcreteN d ^ (3 - 1) *
                  Abound slack d ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  L2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  Q2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.Q w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanRatio_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM
      (R := R) (eps := eps) (k := 3) (by norm_num) hε
      hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan M hOne hMany hVariance
      hMeanCompare hcUpper hUpperExpTail hUpperWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three ratio-Catalan endpoint with named average geometry.

This wrapper keeps the sharp ratio-parametric Catalan input, upper exponential
tail, explicit upper mixed-word estimate, and scalar branch limits visible.
Only the raw direct geometry block is supplied internally from the named
average-geometry packet. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanRatio_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      ∀ lam : ℝ,
        Tendsto
          (fun d : ℕ => ((R.sample d - 1 : ℕ) : ℝ) / (lowerConcreteN d : ℝ))
          atTop (nhds lam) →
        lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound
          R.sample lam 3 m Wcard Cmodel)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) 3 Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed 3 d)
                (upperSlackRadius (spikeRoot 3 eps) R.lam slack) →
            ∀ w : Fin 3 → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) 3 w)
    (hUpperOneLinearTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * L1bound slack d)
          atTop (nhds 0))
    (hUpperOneQuadraticTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * Q1bound slack d)
          atTop (nhds 0))
    (hUpperMultiTerm :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin 3 → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            Tendsto
              (fun d =>
                upperConcreteN d ^ (3 - 1) *
                  Abound slack d ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  L2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  Q2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.Q w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanRatio_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
    R hε
    (PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
    m Wcard Cmodel hExplicitCatalan M hOne hMany hVariance
    hMeanCompare hcUpper hUpperExpTail hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three upper endpoint with the Catalan side stated as a direct
`D / d` estimate around the explicit center `1 + 3 / lam`.

Compared with the preceding wrapper, this removes the generic diagram
parameters `m`, `Wcard`, and `Cmodel` from the article-facing route.  The
remaining mean-side input is the direct statement that the deleted-column
third moment is eventually within `D / d` of `1 + 3 * lam⁻¹` for every limiting
deleted-column aspect ratio `lam`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanDOverD_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) 3 Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed 3 d)
                (upperSlackRadius (spikeRoot 3 eps) R.lam slack) →
            ∀ w : Fin 3 → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) 3 w)
    (hUpperOneLinearTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * L1bound slack d)
          atTop (nhds 0))
    (hUpperOneQuadraticTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * Q1bound slack d)
          atTop (nhds 0))
    (hUpperMultiTerm :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin 3 → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            Tendsto
              (fun d =>
                upperConcreteN d ^ (3 - 1) *
                  Abound slack d ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  L2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  Q2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.Q w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases
    lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
      R.sample hThreeCatalan with
    ⟨Cmodel, hExplicitCatalan⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanRatio_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
      R hε hLemma43AutoHeightBandsDirectGainSup
      0 1 Cmodel hExplicitCatalan M hOne hMany hVariance
      hMeanCompare hcUpper hUpperExpTail hUpperWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three upper endpoint with the Catalan side stated as a direct
`D / d` estimate and the height-band geometry supplied by the named average
geometry packet. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanDOverD_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          ∀ ⦃X Y :
              SampleMatrix
                (PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))⦄,
            |backgroundMomentValue
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) 3 Y -
              upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d| ≤ upperCanonicalTau slack d ∧
              PptFactorization.HighProbabilityBounds.sampleOpNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  Y ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / Real.sqrt (upperConcreteN d) ∧
              opNorm
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (gamma (densityMatrix Y)) ≤
                upperConcreteM
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                      (R.sample d))
                    slack d / upperConcreteN d →
            frobeniusNorm
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (X - Y) ≤
              sharpSphericalRadius
                (upperConcreteN d) (spikeSpeed 3 d)
                (upperSlackRadius (spikeRoot 3 eps) R.lam slack) →
            ∀ w : Fin 3 → LocalExpansionLetter,
              localWordIsMixed w →
                |localWordScaledTraceTerm
                    (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                    (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                    (upperConcreteN d)
                    (localBackground
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y)
                    (localLinear
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      Y (X - Y))
                    (localQuadratic
                      (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                      (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                      (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                        (R.sample d))
                      (X - Y))
                    w| ≤
                  localExpansionMixedWordEnvelopeTerm
                    (upperConcreteN d) (Abound slack d) (L2bound slack d)
                    (L1bound slack d) (Q2bound slack d) (Q1bound slack d) 3 w)
    (hUpperOneLinearTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * L1bound slack d)
          atTop (nhds 0))
    (hUpperOneQuadraticTerm :
      ∀ slack : ℝ, 0 < slack →
        Tendsto
          (fun d =>
            upperConcreteN d ^ (3 - 1) *
              Abound slack d ^ (3 - 1) * Q1bound slack d)
          atTop (nhds 0))
    (hUpperMultiTerm :
      ∀ slack : ℝ, 0 < slack →
        ∀ w : Fin 3 → LocalExpansionLetter,
          localWordIsMixed w →
          ¬ localWordHasOneLinearDefect w →
          ¬ localWordHasOneQuadraticDefect w →
            Tendsto
              (fun d =>
                upperConcreteN d ^ (3 - 1) *
                  Abound slack d ^
                    localWordLetterCount LocalExpansionLetter.A w *
                  L2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.L w *
                  Q2bound slack d ^
                    localWordLetterCount LocalExpansionLetter.Q w)
              atTop (nhds 0)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanDOverD_varianceStack_upperExponentialTail_meanCompare_upperMixedWordExplicit_upperScalarLimitsExplicit_lowerPTDirectScalarCases_normalizedM_k3
    R hε
    (PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
    hThreeCatalan M hOne hMany hVariance hMeanCompare hcUpper
    hUpperExpTail hUpperWord hUpperOneLinearTerm hUpperOneQuadraticTerm
    hUpperMultiTerm

/-- Length-three upper endpoint with the lower mixed side stated at the
same-error mixed frontier.

This is the sharper companion to the fixed-envelope direct-scalar endpoint
below.  The lower mixed input is the exact pair used by the argument: an
on-sphere mixed local-expansion envelope and eventual smallness for the same
error sequence.  The upper mixed side is still supplied by branch envelope
dominations plus the three scalar branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases
    lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
      R.sample
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_atBalancedRatio
        R hThreeCatalan) with
    ⟨Cmodel, hExplicitCatalan⟩
  have hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 :=
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
      R.sample 3 0 1 Cmodel hExplicitCatalan
  have hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3 :=
    UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
      (R := R) (eps := eps) (k := 3)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (by norm_num) hε
      hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num) hε hLemma43AutoHeightBandsDirectGainSup
      hMeanError hLowerMixedFrontier hVariance
      (by simpa [upperConcreteModelMeanSeq] using hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three upper endpoint with the deleted-background variance/Chebyshev
input supplied by the stronger exponential deleted-moment tail.

This is an adapter, not a proof of the variance theorem from nothing: the
visible background-typicality input is now the exponential deleted-background
deviation source, and the polynomial variance/Chebyshev package is built
internally from that source. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_deletedMomentExponential_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hThreeCatalan
    hLowerMixedFrontier
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
      R 3 hDeletedMomentExp)
      hMeanCompare hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
    hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three upper endpoint with balanced-ratio Catalan control and
deleted-background exponential concentration, with geometry and centering
both supplied by named packets. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_deletedMomentExponential_upperExponentialConcentration_meanCompareNamed_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_deletedMomentExponential_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε
    (PptFactorization.AppendixB.lemma43_autoHeightBands_directGainSup_equal_mass_of_autoHeightBands_gainSup_equal_mass_pos_lt_pi
      (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
    hThreeCatalan hLowerMixedFrontier hDeletedMomentExp
    (upperLowerConcreteMeanCompare.raw hMeanCompare)
    hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-form auto-height-band Lemma 4.3 data supplies the direct
block-to-`sSup` geometric input used by the current upper route.

The scalar step is just transitivity: a rectangular block bound at an auxiliary
average `avg`, together with `avg <= sSup`, gives the same block bound with
right-hand side `sSup`. -/
theorem lemma43AutoHeightBandsDirectGainSup_of_averageGainSup
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A)) :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)) := by
  intro n _ hn r hrpos hrpi η hη
  rcases hLemma43AutoHeightBands n hn (r := r) hrpos hrpi (η := η) hη with
    ⟨epsBand, tauSep, hepsBand, htauSep, hA⟩
  refine ⟨epsBand, tauSep, hepsBand, htauSep, ?_⟩
  intro A hHalf hGain
  rcases hA hHalf hGain with
    ⟨Cmodel, pole, a, tauMax, htauMax, hMeas, hMass, hSymm, hBands⟩
  refine ⟨Cmodel, pole, a, tauMax, htauMax, hMeas, hMass, hSymm, ?_⟩
  intro tauBand htauBand hleTau
  rcases hBands htauBand hleTau with ⟨avg, hRect, havg⟩
  unfold SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound at *
  exact hRect.trans havg

/-- Length-three upper endpoint with the geometric input in average-form
Lemma 4.3 shape, the Catalan side stated only at the actual balanced ratio, and
the deleted-background typicality side stated as the variance/Chebyshev stack.

This is the cleanest current article-facing adapter: it removes the generic
diagram constants `m`, `Wcard`, and `Cmodel` and replaces the grouped
second-moment tail predicate by the paper-facing variance input.  The remaining
inputs are still genuine theorem-strength assumptions. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε
    (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup hLemma43AutoHeightBands)
    hThreeCatalan hLowerMixedFrontier hVariance hMeanCompare hUpperExp
    hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three upper endpoint with the Catalan side exposed as the finite
diagram `D / d` source and the deleted-background typicality side exposed as
the second-moment Wick/Chebyshev tail.

This is the paper-facing companion to the exponential-tail adapter below: it
uses the polynomial variance packet directly, rather than asking for the
stronger `exp (-c d^2)` concentration source. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 :=
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
      R.sample 3 m Wcard Cmodel hExplicitCatalan
  have hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3 :=
    UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
      (R := R) (eps := eps) (k := 3)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (by norm_num) hε
      hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num) hε hLemma43AutoHeightBandsDirectGainSup
      hMeanError hLowerMixedFrontier
      (by
        simpa [deletedColumnSphericalMoment_variance_le_const_div_d4] using
          hMomentSecond)
      (by simpa [upperConcreteModelMeanSeq] using hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three upper endpoint with the geometric input stated in the natural
average-form auto-height-band Lemma 4.3 shape.

The average-form data is converted internally to the direct block-to-`sSup`
shape by `lemma43AutoHeightBandsDirectGainSup_of_averageGainSup`, so the
article-facing route no longer has to ask for a rectangular block lower bound
already written with the supremum as its right-hand side. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε
    (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hMomentSecond
    hMeanCompare hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
    hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three repaired upper route with the article-facing Catalan and
variance inputs exposed directly.

This is the non-vacuous companion to the refuted fixed-`M` lower PT branch:
the lower mixed side is the honest same-error frontier
`lowerConcreteMixedErrorFrontier`, while the mean side is the direct
ratio-parametric three-Catalan `D / d` input and the background concentration
side is the variance/Chebyshev stack. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases
    lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
      R.sample hThreeCatalan with
    ⟨Cmodel, hExplicitCatalan⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
      R hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
      0 1 Cmodel hExplicitCatalan hLowerMixedFrontier
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R 3 hVariance)
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three repaired upper route with both mixed sides stated as honest
mixed-remainder frontiers.

This is the non-vacuous companion to the branch-envelope route above.  The
lower mixed side is the same-error frontier
`lowerConcreteMixedErrorFrontier`; the upper mixed side is the model mixed
remainder input itself, rather than the inconsistent length-three package
combining branch envelope dominations with scalar limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 := by
    rcases
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
        R.sample hThreeCatalan with
      ⟨Cmodel, hExplicitCatalan⟩
    exact
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample 3 0 1 Cmodel hExplicitCatalan
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε
      (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup
        (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
      hMeanError hLowerMixedFrontier hVariance
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three repaired upper route with the mean bridge stated as the target
probability comparison actually used by the one-column pipeline.

This is weaker and more literal than `upperLowerConcreteMeanCompare`: it asks
directly that the deleted-background lower target is eventually dominated by
the actual upper target.  The centering inequality remains available as one
sufficient adapter, but it is no longer theorem-facing on this route. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hTargetCompare :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R 3) 3 d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R 3) 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 := by
    rcases
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
        R.sample hThreeCatalan with
      ⟨Cmodel, hExplicitCatalan⟩
    exact
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample 3 0 1 Cmodel hExplicitCatalan
  have hMeanBound :
      lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded R 3 :=
    lowerConcreteDeletedBackgroundMeanPositivePartEventuallyBounded_of_deletedColumnCatalanErrorBoundFromRatio
      R 3 hMeanError
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_meanBound_varianceStack_targetCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedError
      R (by norm_num : 3 ≤ 3) hε
      (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup
        (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands))
      hMeanBound errMix hLowerMixedFrontier.1 hLowerMixedFrontier.2 hVariance
      hTargetCompare hUpperExp hUpperMixed

/-- Length-three repaired upper route with the Catalan input stated only at the
balanced ratio of the actual model.

This is weaker and more literal than the ratio-parametric Catalan endpoint:
it asks for the eventual `D / d` estimate around `1 + 3 * R.lam⁻¹`, not for
the same estimate uniformly over every possible limiting aspect ratio.  The
ratio-parametric version remains available as an adapter target. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hTargetCompare :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R 3) 3 d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R 3) 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBands
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_atBalancedRatio
      R hThreeCatalanAtRatio)
    hLowerMixedFrontier hVariance hTargetCompare hUpperExp hUpperMixed

/-- Length-three repaired upper route with both lower mean/background inputs
stated in their literal consumed forms.

Compared with the variance-stack wrapper above, this exposes the exact
Chebyshev/Wick lower-background tail packet used to construct the lower
background half-mass set.  The paper-facing variance predicate remains an
adapter because, at this layer, it is definitionally the same tail frontier. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentration_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hTargetCompare :
      ∀ᶠ d in atTop,
        lowerConcreteTargetProb R (lowerConcreteEps eps)
            (lowerConcreteDeletedBackgroundMean R 3) 3 d ≤
          lowerConcreteTargetProb R (fun _d : ℕ => eps)
            (upperConcreteModelMeanSeq R 3) 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBands hThreeCatalanAtRatio
    hLowerMixedFrontier hMomentTail hTargetCompare hUpperExp hUpperMixed

/-- Length-three repaired upper route with the upper concentration input stated
as an existential rate.

The proof only needs that some positive exponential moment-deviation rate
exists; the numerical witness `cUpper` is not part of the paper-facing
frontier. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hTargetCompare : upperLowerConcreteTargetCompare R eps 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentration_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail hTargetCompare.raw hUpperExp hUpperMixed

/-- Length-three repaired upper route with the lower mixed frontier stated
existentially.

The proof does not care which error sequence witnesses the lower mixed
frontier.  It only needs that some common error controls both the local
expansion envelope and the eventual smallness estimate. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_targetCompare_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hTargetCompare : upperLowerConcreteTargetCompare R eps 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_targetCompare_upperMixedRemainder_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail hTargetCompare hUpperExp hUpperMixed

/-- Length-three repaired upper route with the target comparison supplied by
the scalar centering comparison.

This replaces the theorem-facing probability bridge by the concrete scalar
statement
`upperConcreteModelMeanSeq R 3 d <= lowerConcreteDeletedBackgroundMean R 3 d`
eventually.  The conversion from this scalar inequality to the target
probability comparison is only event monotonicity. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_meanCompare_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_targetCompare_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail
      (upperLowerConcreteTargetCompare_of_meanCompare R (eps := eps) (k := 3) hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three repaired upper route with the mean comparison supplied by the
signed Catalan-gap packet.

This exposes the quantitative signed estimate that is enough to compare the
two centerings: the deleted-column mean is within `D / d` of the Catalan
center, while the upper full-model mean is below the same center by at least
`E / d` with `D <= E`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_signedCatalanGap_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_meanCompare_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail
      (upperLowerConcreteMeanCompare_three_of_signedCatalanGap R hSignedGap)
      hUpperExp hUpperMixed

/-- Length-three repaired upper route with the whole mean side supplied by the
signed Catalan-gap packet.

Compared with the preceding wrapper, this no longer asks separately for the
deleted-column `D / d` Catalan estimate.  That estimate is already one clause of
the signed gap; the same packet also supplies the one-sided upper/deleted mean
comparison. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_signedCatalanGap_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_signedCatalanGap
      R hSignedGap)
    hLowerMixedFrontier hMomentTail hSignedGap hUpperExp hUpperMixed

/-- Length-three repaired upper route with the mean side bundled as a signed
Catalan gap and the lower background side stated as the variance estimate.

The second-moment/Wick bad-set tail is obtained internally from
`deletedColumnSphericalMoment_variance_le_const_div_d4 R 3`, so the visible
background input is the paper-facing variance/Chebyshev statement. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hSignedGap hLowerMixedFrontier
    (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R 3 hVariance)
    hUpperExp hUpperMixed

/-- Length-three repaired upper route with the mean/background side bundled and
the upper mixed input split into word bounds plus scalar envelope limits.

This is the mixed-frontier version of the signed-gap/variance route: the broad
upper mixed-remainder predicate is supplied internally by the finite local-word
summation lemma from a deterministic model-level word bound and the scalar
`o(1)` envelope package. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_modelMixedWordBound_mixedTermLimit_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hSignedGap hLowerMixedFrontier hVariance
    hUpperExp
    (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
      (R := R) (eps := eps) (k := 3)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Length-three repaired upper route with the upper mixed scalar limit split
into the three defect cases on the signed-gap/variance route.

This is only finite-case bookkeeping: the bundled scalar mixed-term predicate
is supplied internally from the one-linear, one-quadratic, and multi-defect
limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_modelMixedWordBound_mixedTermLimit_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hSignedGap hLowerMixedFrontier hVariance
    hUpperExp hUpperWord
    (UpperConcreteModelMixedTermLimit_of_caseLimits
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three repaired upper route with signed mean, variance background,
and canonical actual-model upper word bounds.

The deterministic canonical word estimates supply the model-level mixed-word
bound internally.  The only upper mixed inputs left on this route are the three
canonical scalar branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_canonicalWordBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hSignedGap hLowerMixedFrontier hVariance
    hUpperExp
    (UpperConcreteModelMixedWordBound_of_caseBounds
      R
      (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
        R (by norm_num : 3 ≤ 3) hε)
      (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
        R (by norm_num : 3 ≤ 3) hε)
      (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
        R (by norm_num : 3 ≤ 3) hε))
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- The canonical scalar-limit packet on the signed-gap/variance endpoint is
inconsistent at length three.

The signed mean-side cleanup and variance-facing background cleanup do not
change the upper local-spike obstruction: the canonical one-linear scalar limit
already contradicts the checked actual-model growth. -/
theorem
    upper_concrete_signedGap_variance_canonicalWordBounds_endpoint_caseTerm_packet_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    False := by
  let _ := hUpperOneQuadraticTerm
  let _ := hUpperMultiTerm
  exact
    upperConcreteModel_oneLinearMixedTermLimit_not_canonical
      (R := R) hε hUpperOneLinearTerm

/-- Length-three repaired upper route with the lower `D / d` Catalan estimate
and the upper-model signed margin separated.

Compared with the signed-gap endpoint, this consumes the already visible
deleted-column `D / d` input for the lower side and leaves only the
upper-model margin below the Catalan center as the new centering comparison
work. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_signedCatalanGap_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail
      (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_upperMargin
        R hThreeCatalanAtRatio hUpperMeanMargin)
      hUpperExp hUpperMixed

/-- Length-three repaired upper route with the upper mean-margin input replaced
by the asymptotic scalar deficit from the Catalan center.

The mean-side input is now the readable statement
`d * ((1 + 3 / lambda) - m_upper(d)) -> +infty`; the previous arbitrary
`E / d` margin is supplied by scalar order bookkeeping. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail
      (upperConcreteModelMeanThreeCatalanUpperMarginFor_of_scaledDeficitTendsToTop
        R hUpperMeanDeficit)
      hUpperExp hUpperMixed

/-- Length-three repaired upper route with the background typicality input
exposed as the paper-facing variance estimate.

This is the variance-facing form of
`...secondMomentWickTail...upperMeanScaledDeficit...`: the grouped
second-moment/Wick tail is obtained internally by the Chebyshev converter from
`deletedColumnSphericalMoment_variance_le_const_div_d4 R 3`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R 3 hVariance)
      hUpperMeanDeficit hUpperExp hUpperMixed

/-- Length-three repaired upper route with the upper full-model concentration
input unfolded on the clean mixed-remainder surface.

This replaces the existential concentration package by the literal positive
exponent and eventual exponential deviation estimate for the closed background
moment event. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ} (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            upperConcreteModelExponentialMomentEnvelope cUpper slack d)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hVariance hUpperMeanDeficit
      (⟨cUpper, ⟨hcUpper, hUpperExpTail⟩⟩ :
        ∃ cUpper : ℝ,
          UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
      hUpperMixed

/-- Length-three repaired upper route with the lower mixed frontier supplied
from the two direct partial-transpose scalar estimates.

The lower mixed error sequence, finite PT word budget, and eventual smallness
are all assembled internally.  The theorem-facing lower mixed inputs are the
one-`Q` and many-`Q` direct scalar bounds. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ} (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            upperConcreteModelExponentialMomentEnvelope cUpper slack d)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio
      ⟨fun a slack d => lowerPartialTransposeMixedErrorD 3 (a + slack) M d,
        lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases
          (R := R) (k := 3) (ε := eps) (M := M)
          (by norm_num : 3 ≤ 3) hε hM hOne hMany⟩
      hVariance hUpperMeanDeficit hcUpper hUpperExpTail hUpperMixed

/-- Length-three repaired upper route with the upper mixed remainder split into
the model word bound and the scalar mixed-term limit.

This is the cleanest current endpoint surface before proving the remaining
analytic leaves: the lower mixed side is reduced to the two direct PT scalar
estimates, the upper concentration side is the direct exponential tail, and the
upper local-spike side is the deterministic word estimate plus scalar smallness. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_modelMixedWordBound_mixedTermLimit_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ} (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            upperConcreteModelExponentialMomentEnvelope cUpper slack d)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerPTDirectScalarCases_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hM hOne hMany
      hVariance hUpperMeanDeficit hcUpper hUpperExpTail
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
        (R := R) (eps := eps) (k := 3)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Length-three repaired upper route with the upper scalar mixed-term limit
split into the three finite defect cases.

The bundled scalar smallness input is assembled internally from the one-linear,
one-quadratic, and remaining multi-defect scalar limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ} (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            upperConcreteModelExponentialMomentEnvelope cUpper slack d)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_modelMixedWordBound_mixedTermLimit_lowerPTDirectScalarCases_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hM hOne hMany
      hVariance hUpperMeanDeficit hcUpper hUpperExpTail hUpperWord
      (UpperConcreteModelMixedTermLimit_of_caseLimits
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three repaired upper route with the upper concentration input kept
as the reusable exponential concentration predicate.

This is the named-concentration companion to
`...upperExponentialTail...caseTermLimits...lowerPTDirectScalarCases_k3`: the
positive exponent and pointwise exponential tail are unpacked internally. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentration_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ} (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hM hOne hMany
      hVariance hUpperMeanDeficit hUpperExp.1 hUpperExp.2 hUpperWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three repaired upper route with the lower partial-transpose mixed
side reduced to its two exact scale comparisons.

The direct one-`Q` and many-`Q` local trace estimates are assembled internally.
The many-`Q` scale comparison also supplies nonnegativity of the fixed PT
envelope parameter. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTScaleComparisons_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ}
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ} (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            upperConcreteModelExponentialMomentEnvelope cUpper slack d)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hM : 0 ≤ M :=
    lowerConcretePTMixedWordManyQScaleComparison_nonneg_M
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 3 ≤ 3) hε hManyScale
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTDirectScalarCases_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hM
      (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
        (R := R) (k := 3) (ε := eps) (M := M)
        (by norm_num : 3 ≤ 3) hε hOneScale)
      (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
        (R := R) (k := 3) (ε := eps) (M := M)
        (by norm_num : 3 ≤ 3) hε hManyScale)
      hVariance hUpperMeanDeficit hcUpper hUpperExpTail hUpperWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three repaired upper route with the upper mixed-remainder input
replaced by the deterministic word-by-word bound plus scalar envelope limits.

This exposes the local-spike work as the two mathematical tasks:
every mixed word is bounded by its envelope, and every mixed-word envelope term
tends to zero. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_mixedTermLimit_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail hUpperMeanDeficit hUpperExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
        (R := R) (eps := eps) (k := 3)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Length-three repaired upper route with both the background typicality and
upper mixed-remainder inputs exposed in paper-facing form.

The background side is the deleted-background variance estimate; the upper
mixed side is the deterministic word-by-word envelope plus the scalar statement
that every envelope term tends to zero. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_mixedTermLimit_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hVariance hUpperMeanDeficit hUpperExp
      (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
        (R := R) (eps := eps) (k := 3)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Length-three repaired upper route with the upper mixed scalar limit split
into the three defect cases.

Every mixed local word is either a one-linear-defect word, a one-quadratic-defect
word, or a remaining multi-defect word.  This wrapper keeps the model-level
word bound visible and replaces the bundled scalar limit by those three
casewise limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_mixedTermLimit_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail hUpperMeanDeficit hUpperExp hUpperWord
      (UpperConcreteModelMixedTermLimit_of_caseLimits
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three repaired upper route with variance-facing background
typicality and branchwise upper mixed scalar limits.

This keeps the local-spike frontier split into one-linear, one-quadratic, and
multi-defect scalar limits, while the background bad-set budget is supplied
from the paper-facing variance estimate. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_mixedTermLimit_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hVariance hUpperMeanDeficit hUpperExp hUpperWord
      (UpperConcreteModelMixedTermLimit_of_caseLimits
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three repaired upper route with the canonical actual-model upper
mixed word bounds wired in.

For the canonical envelopes, the local matrix estimates supply the word-bound
side of the upper mixed input.  The remaining canonical upper mixed inputs are
exactly the three scalar defect-case limits; these are the known obstruction for
the canonical route. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_canonicalWordBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail hUpperMeanDeficit hUpperExp
      (UpperConcreteModelMixedWordBound_of_caseBounds
        R
        (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
          R (by norm_num : 3 ≤ 3) hε)
        (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
          R (by norm_num : 3 ≤ 3) hε)
        (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
          R (by norm_num : 3 ≤ 3) hε))
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three repaired upper route with canonical actual-model word bounds
and variance-facing background typicality.

This is still a diagnostic route: the canonical scalar-limit packet below is
known inconsistent.  The adapter only removes the extra Wick-tail packaging
from the background side. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_canonicalWordBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hVariance hUpperMeanDeficit hUpperExp
      (UpperConcreteModelMixedWordBound_of_caseBounds
        R
        (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
          R (by norm_num : 3 ≤ 3) hε)
        (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
          R (by norm_num : 3 ≤ 3) hε)
        (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
          R (by norm_num : 3 ≤ 3) hε))
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- The canonical scalar-limit packet on the current repaired upper endpoint is
inconsistent at length three.

The canonical word-bound half is checked, but the first scalar limit in the
remaining packet is already impossible.  Thus this canonical-envelope endpoint
is a diagnostic route, not a live closure route. -/
theorem
    upper_concrete_current_canonicalWordBounds_endpoint_caseTerm_packet_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    False := by
  let _ := hUpperOneQuadraticTerm
  let _ := hUpperMultiTerm
  exact
    upperConcreteModel_oneLinearMixedTermLimit_not_canonical
      (R := R) hε hUpperOneLinearTerm

/-- The current repaired upper endpoint cannot use the canonical actual-model
one-quadratic scalar limit at length three.

This records the same obstruction at the endpoint level for the one-quadratic
branch: the canonical scalar term diverges along the spike slack, so it cannot
be one of the zero-limit scalar inputs for the local-spike certificate. -/
theorem
    upper_concrete_current_canonicalWordBounds_endpoint_oneQuadratic_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3)) :
    False :=
  upperConcreteModel_oneQuadraticMixedTermLimit_not_canonical
    (R := R) hε hUpperOneQuadraticTerm

/-- The current repaired upper endpoint cannot use the canonical actual-model
multi-defect scalar limit at length three.

The pure `L,L,L` word is already a valid multi-defect word, and the canonical
scalar term for that word diverges along the spike slack. -/
theorem
    upper_concrete_current_canonicalWordBounds_endpoint_multiDefect_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    False :=
  upperConcreteModel_multiDefectMixedTermLimit_not_canonical
    (R := R) hε hUpperMultiTerm

/-- Length-three repaired upper route with the broad upper mixed-remainder input
split into the three branch envelope dominations and three branch scalar
limits.

This is the sharper companion to
`..._upperMeanCatalanMargin_upperMixedRemainder_...`: the lower side remains the
honest same-error mixed frontier, while the upper local-spike input is exposed
as its one-linear, one-quadratic, and multi-defect branches. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentTail :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hMomentTail hUpperMeanMargin hUpperExp
      (UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
        (R := R) (eps := eps) (k := 3)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by norm_num : 3 ≤ 3) hε
        hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Branch-envelope companion route with variance-facing background
typicality.

The route is diagnostic for the current canonical branch envelopes, but its
background input is now the paper-facing variance estimate rather than the
grouped Wick/Chebyshev tail. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R 3 hVariance)
      hUpperMeanMargin hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
      hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Branch-envelope route with the lower mixed frontier unpacked into its
word-by-word proof obligations.

The lower mixed input is not an abstract mystery here: it is built from
pointwise mixed-word control on the Frobenius sphere, a finite budget summing
those word bounds into one error sequence, and eventual smallness of that same
error sequence. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedWordBoundsBudget_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {bound : ℝ → ℝ → ℕ → (Fin 3 → LocalExpansionLetter) → ℝ}
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps bound)
    (hLowerMixedBudget :
      lowerConcreteMixedWordBudgetWithError R 3 eps bound errMix)
    (hLowerMixedSmall :
      lowerConcreteMixedErrorEventuallySmall 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix :=
    ⟨errMix,
      lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
        (R := R) (k := 3) (ε := eps) (by norm_num : 1 ≤ 3)
        bound errMix hLowerMixedWord hLowerMixedBudget hLowerMixedSmall⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedFrontier
      hVariance hUpperMeanMargin hUpperExp hUpperOneLinearDom
      hUpperOneQuadraticDom hUpperMultiDom hUpperOneLinearTerm
      hUpperOneQuadraticTerm hUpperMultiTerm

/-- Branch-envelope route with the lower mixed scalar smallness reduced to
termwise convergence of the mixed-word envelopes.

The finite budget is closed by choosing the mixed error to be the exact filtered
sum of mixed-word bounds.  The scalar `o(1)` part is then pure finite-sum
bookkeeping from termwise convergence. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedTermwiseSmall_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {bound : ℝ → ℝ → ℕ → (Fin 3 → LocalExpansionLetter) → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps bound)
    (hLowerMixedTermwise :
      ∀ a : ℝ, spikeRoot 3 eps < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ w : Fin 3 → LocalExpansionLetter,
            localWordIsMixed w →
              Tendsto (fun d : ℕ => bound a slack d w) atTop (nhds 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedWordBoundsBudget_k3
    R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedWord
    (lowerConcreteMixedWordBudgetWithExactSum R 3 eps bound)
    (lowerConcreteMixedErrorEventuallySmall_of_filteredSum_termwise_tendsto
      hLowerMixedTermwise)
    hVariance hUpperMeanMargin hUpperExp hUpperOneLinearDom
    hUpperOneQuadraticDom hUpperMultiDom hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Branch-envelope route with the lower mixed word estimates supplied by the
two fixed-`M` partial-transpose scalar leaves.

The lower mixed side is closed internally from the one-`Q` and many-`Q`
direct scalar estimates: they give the pointwise mixed-word bound, and the
literal partial-transpose envelopes tend to zero term by term. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ} (hM : 0 ≤ M)
    (hLowerOneQ :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hLowerManyQ :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d) :=
    lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 0 < 3) hε hM hLowerOneQ hLowerManyQ
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerMixedTermwiseSmall_k3
      R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixedWord
      (lowerPartialTransposeMixedWordBoundD_termwise_tendsto
        (k := 3) (ε := eps) (M := M) (by norm_num) hε hM)
      hVariance hUpperMeanMargin hUpperExp hUpperOneLinearDom
      hUpperOneQuadraticDom hUpperMultiDom hUpperOneLinearTerm
      hUpperOneQuadraticTerm hUpperMultiTerm

/-- Branch-envelope route with the fixed-`M` lower PT leaves stated as scalar
scale comparisons.

The local trace estimates convert the two scale comparisons into the direct
one-`Q` and many-`Q` PT scalar leaves used by
`...lowerPTDirectScalarCases_k3`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTScaleComparisons_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    {M : ℝ}
    (hLowerOneQScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps M)
    (hLowerManyQScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_k3
    R hε hLemma43AutoHeightBands hThreeCatalanAtRatio
    (lowerConcretePTMixedWordManyQScaleComparison_nonneg_M
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num) hε hLowerManyQScale)
    (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num) hε hLowerOneQScale)
    (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num) hε hLowerManyQScale)
    hVariance hUpperMeanMargin hUpperExp hUpperOneLinearDom
    hUpperOneQuadraticDom hUpperMultiDom hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- The fixed-`M` lower PT scale-comparison packet on the branch route is
inconsistent at length three.

This is a route diagnostic, not a refutation of the conditional upper
mechanism.  The obstruction is already in the one-`Q` comparison: it would make
the distinguished `QAA` runtime word eventually dominated by an `o(1)` fixed
PT budget. -/
theorem
    upper_concrete_branchEnvelope_meanMargin_endpoint_lowerPTScaleComparisons_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps M : ℝ} (hε : 0 < eps)
    (hM : 0 ≤ M)
    (hLowerOneQScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps M)
    (hLowerManyQScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps M) :
    False :=
  lowerConcretePTMixedWordScaleComparisons_three_not_uniform
    R hε M hM ⟨hLowerOneQScale, hLowerManyQScale⟩

/-- The branchwise upper-mixed companion route has an inconsistent one-linear
input pair at length three.

This does not refute the upper theorem itself.  It says that this particular
attempt to prove the upper mixed remainder by simultaneously dominating the
actual-model one-linear canonical term and forcing the dominating envelope to
tend to zero cannot work. -/
theorem
    upper_concrete_branchEnvelope_meanMargin_endpoint_oneLinear_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound) :
    False :=
  upperConcreteModel_oneLinearDom_and_termLimit_impossible
    R hε ⟨hUpperOneLinearDom, hUpperOneLinearTerm⟩

/-- The branchwise upper-mixed companion route has an inconsistent
one-quadratic input pair at length three.

As in the one-linear branch, the canonical actual-model one-quadratic scalar
term diverges along the spike slack.  A dominating abstract envelope cannot
also tend to zero. -/
theorem
    upper_concrete_branchEnvelope_meanMargin_endpoint_oneQuadratic_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound) :
    False :=
  upperConcreteModel_oneQuadraticDom_and_termLimit_impossible
    R hε ⟨hUpperOneQuadraticDom, hUpperOneQuadraticTerm⟩

/-- The branchwise upper-mixed companion route has an inconsistent multi-defect
input pair at length three.

The pure `L,L,L` word is already a multi-defect word.  For that word, the
canonical actual-model scalar term diverges, so domination by a zero-limit
abstract envelope is impossible. -/
theorem
    upper_concrete_branchEnvelope_meanMargin_endpoint_multiDefect_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L2bound Q2bound : ℝ → ℕ → ℝ}
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    False :=
  upperConcreteModel_multiDefectDom_and_termLimit_impossible
    R hε ⟨hUpperMultiDom, hUpperMultiTerm⟩

/-- The full branch-envelope plus case-limit packet on this upper-mixed
companion route is inconsistent at length three.

The contradiction already appears in the one-linear branch: a scalar envelope
which dominates the actual-model one-linear canonical term cannot also tend to
zero.  Thus this branch-envelope endpoint is diagnostic, not a live route for
closing the upper mixed remainder. -/
theorem
    upper_concrete_branchEnvelope_meanMargin_endpoint_casePacket_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    False := by
  let _ := hUpperOneQuadraticDom
  let _ := hUpperMultiDom
  let _ := hUpperOneQuadraticTerm
  let _ := hUpperMultiTerm
  exact
    upper_concrete_branchEnvelope_meanMargin_endpoint_oneLinear_input_impossible_k3
      R hε hUpperOneLinearDom hUpperOneLinearTerm

/-- Length-three upper endpoint with the Catalan side exposed as the finite
diagram `D / d` source.

Compared with the balanced-ratio `threeCatalan` endpoint, this keeps the
crossing/spherical-correction estimate visible instead of first packaging it
as the direct length-three rate statement.  This is useful for proof work:
the finite-diagram bound is the explicit combinatorial/asymptotic source that
supplies the Catalan-error packet. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_deletedMomentExponential_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hDeletedMomentExp :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier
    (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_exponentialDeviationTailBound
      R 3 hDeletedMomentExp)
    hMeanCompare hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
    hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the background moment tail
fed directly by the deleted-column variance estimate.

This is the same route as the preceding exponential-tail wrapper, but exposes
the usable Chebyshev-scale input
`Var(F_{d,3}) ≤ C d^{-4}` at the frontier. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier
    (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R 3 hVariance)
    hMeanCompare hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
    hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the mean comparison supplied
by the signed Catalan gap.

The explicit deleted-column diagram estimate gives the lower \(D/d\) Catalan
side, and the scaled upper Catalan deficit gives the upper side.  Thus the raw
mean-comparison assumption is generated internally. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentration_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hVariance
    (upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_scaledDeficit
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R
        (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
          R.sample m Wcard Cmodel hExplicitCatalan))
      hUpperMeanDeficit)
    hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with only existence of an upper
exponential concentration rate.

The proof never uses the numerical value of the rate, only that some positive
rate exists. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentration_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hVariance
      hUpperMeanDeficit hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
      hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the lower mixed frontier
stated existentially.

The proof only needs a common lower mixed error function; its particular name
and formula are not part of the upper-rate statement. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBandsDirectGainSup
      m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hVariance
      hUpperMeanDeficit hUpperExp hUpperOneLinearDom hUpperOneQuadraticDom
      hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the upper mixed side stated
as the actual mixed-remainder input.

This is the live local-spike shape: the branch-envelope decomposition is an
adapter for proving the mixed remainder, not part of the upper-rate mechanism
itself. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_scaledDeficit
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R
        (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
          R.sample m Wcard Cmodel hExplicitCatalan))
      hUpperMeanDeficit
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample 3 m Wcard Cmodel hExplicitCatalan)
      hLowerMixedFrontier hVariance
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp hUpperMixed

/-- Direct-gain version of the finite-sphere height-band input used by the
current upper bridge. -/
abbrev finRealSphereAutoHeightBandsDirectGainSup : Prop :=
  ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
      ∀ ⦃η : ℝ⦄, 0 < η →
        ∃ epsBand tauSep : ℝ,
          0 < epsBand ∧
            0 < tauSep ∧
              ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                      (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                        (PptFactorization.AppendixB.finRealSphereNorthPole n :
                          PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                  PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                    (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                ∃ Cmodel pole a tauMax,
                  0 < tauMax ∧
                    MeasurableSet Cmodel ∧
                      (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                          Cmodel =
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                          A ∧
                        epsBand ≤
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                            (symmDiff Cmodel A) ∧
                          ∀ ⦃tauBand : ℝ⦄,
                            0 < tauBand → tauBand ≤ tauMax →
                              SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                n tauSep
                                (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                  Cmodel A
                                  (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                    n pole a tauBand))
                                (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                  Cmodel A
                                  (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                    n pole a tauBand))
                                (sSup
                                  (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                    n r A))

/-- Named average-form geometry supplies the named direct-gain geometry. -/
theorem finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup) :
    finRealSphereAutoHeightBandsDirectGainSup :=
  lemma43AutoHeightBandsDirectGainSup_of_averageGainSup
    (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)

/-- Length-three finite-diagram upper endpoint where the clean upper mixed
remainder is supplied from a single model-level mixed-word estimate and the
three scalar branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound
        R eps 3 Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hVariance
    hUpperMeanDeficit hUpperExp
    (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_caseTermLimits
      R (by norm_num : 1 ≤ 3) hUpperWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Average-geometry version of the clean direct-height-band endpoint.

The direct-gain geometric packet is supplied from the named average-gain
packet, so this route exposes one canonical geometry input rather than two
parallel forms. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound
        R eps 3 Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hVariance
    hUpperMeanDeficit hUpperExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the deleted-background
typicality input exposed as the grouped second-moment Wick/Chebyshev packet.

The variance-style tail used by the clean endpoint is obtained internally from
the same second-moment frontier, so the theorem-facing assumption is the
combinatorial estimate that still has to be supplied. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound
        R eps 3 Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
      R 3 hMomentSecond)
    hUpperMeanDeficit hUpperExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-geometry version of the second-moment Wick/Chebyshev direct-height
endpoint.

The grouped second-moment input remains theorem-facing; only the geometry
adapter is hidden by using the canonical average-form geometric packet. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound
        R eps 3 Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hLowerMixedFrontier hMomentSecond
    hUpperMeanDeficit hUpperExp hUpperWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the lower mixed frontier
supplied by a concrete pointwise partial-transpose mixed-word estimate.

For this route the existential lower error function is the literal
partial-transpose error.  Its finite budget and eventual smallness are supplied
by the lower mixed-word infrastructure; the theorem-facing input is the
pointwise word estimate on the Frobenius sphere. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound
        R eps 3 Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan
    ⟨fun a slack d => lowerPartialTransposeMixedErrorD 3 (a + slack) M d,
      lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
        (R := R) (k := 3) (ε := eps) (M := M)
        (by norm_num : 3 ≤ 3) hε hM hLowerWord⟩
    hMomentSecond hUpperMeanDeficit hUpperExp hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-geometry version of the lower PT pointwise mixed-word route.

The pointwise PT word estimate remains theorem-facing; the lower mixed error
frontier and the direct geometry packet are supplied internally. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound
        R eps 3 Abound L2bound L1bound Q2bound Q1bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hMomentSecond
    hUpperMeanDeficit hUpperExp M hM hLowerWord hUpperWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the upper mixed-word bound
split into the three deterministic branches.

The model-level upper mixed-word input is assembled internally from the
one-linear, one-quadratic, and multi-defect word estimates.  The three scalar
branch limits remain visible because they are the separate asymptotic
smallness checks for those branches. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_caseMixedWordBounds_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_modelMixedWordBound_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hMomentSecond
    hUpperMeanDeficit hUpperExp M hM hLowerWord
    (UpperConcreteModelMixedWordBound_of_caseBounds
      R hUpperOneLinearWord hUpperOneQuadraticWord hUpperMultiWord)
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-geometry version of the upper mixed branch-word route.

The three upper branch word estimates remain visible; the aggregate upper
mixed-word bound and direct geometry packet are supplied internally. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_caseMixedWordBounds_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_caseMixedWordBounds_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hMomentSecond
    hUpperMeanDeficit hUpperExp M hM hLowerWord hUpperOneLinearWord
    hUpperOneQuadraticWord hUpperMultiWord hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the upper branch word
estimates supplied by scalar envelope dominations.

The local matrix estimates are already packaged in the three branch converters;
what remains theorem-facing here are the three scalar envelope dominations and
the three scalar branch limits. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_caseMixedWordBounds_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    m Wcard Cmodel hExplicitCatalan hMomentSecond
    hUpperMeanDeficit hUpperExp M hM hLowerWord
    (UpperConcreteModelOneLinearMixedWordBound_of_envelopeDomination
      R (by norm_num : 3 ≤ 3) hε hUpperOneLinearDom)
    (UpperConcreteModelOneQuadraticMixedWordBound_of_envelopeDomination
      R (by norm_num : 3 ≤ 3) hε hUpperOneQuadraticDom)
    (UpperConcreteModelMultiDefectMixedWordBound_of_envelopeDomination
      R (by norm_num : 3 ≤ 3) hε hUpperMultiDom)
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-geometry version of the upper scalar-envelope route.

The three scalar envelope dominations and their scalar limits remain visible;
direct geometry and branch word reconstruction are supplied internally. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hMomentSecond
    hUpperMeanDeficit hUpperExp M hM hLowerWord hUpperOneLinearDom
    hUpperOneQuadraticDom hUpperMultiDom hUpperOneLinearTerm
    hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the upper mean input stated
as the direct Catalan margin rather than the stronger scaled-deficit package.

The lower finite-diagram Catalan estimate supplies the deleted-background
`D / d` side; the upper margin supplies an upper-model gap at least as large as
that `D / d` error.  Together they give the mean comparison used by the upper
mechanism. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  let errMix : ℝ → ℝ → ℕ → ℝ :=
    fun a slack d => lowerPartialTransposeMixedErrorD 3 (a + slack) M d
  have hLowerMixedFrontier : lowerConcreteMixedErrorFrontier R 3 eps errMix :=
    lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 3 ≤ 3) hε hM hLowerWord
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_upperMargin
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R
        (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
          R.sample m Wcard Cmodel hExplicitCatalan))
      hUpperMeanMargin
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample 3 m Wcard Cmodel hExplicitCatalan)
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hMomentSecond)
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp
      (UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
        (R := R) (eps := eps) (k := 3)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by norm_num : 3 ≤ 3) hε
        hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Average-geometry version of the upper Catalan-margin endpoint.

The upper mean-margin family remains theorem-facing.  The direct geometry
packet is supplied from the canonical average-form geometric input. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    m Wcard Cmodel hExplicitCatalan hMomentSecond hUpperMeanMargin
    hUpperExp M hM hLowerWord hUpperOneLinearDom hUpperOneQuadraticDom
    hUpperMultiDom hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three finite-diagram upper endpoint with the lower Catalan input
split into the two consequences actually used by the route.

The previous endpoint consumed a full explicit finite-diagram package.  The
upper mechanism only needs (i) the deleted-background Catalan error and (ii)
the length-three `D / d` estimate at the balanced ratio, which combines with
the upper Catalan margin to give the mean comparison. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hCatalanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  let errMix : ℝ → ℝ → ℕ → ℝ :=
    fun a slack d => lowerPartialTransposeMixedErrorD 3 (a + slack) M d
  have hLowerMixedFrontier : lowerConcreteMixedErrorFrontier R 3 eps errMix :=
    lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 3 ≤ 3) hε hM hLowerWord
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_upperMargin
      R hThreeCatalanAtRatio hUpperMeanMargin
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      hCatalanError
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hMomentSecond)
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp
      (UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
        (R := R) (eps := eps) (k := 3)
        (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
        (Q2bound := Q2bound) (Q1bound := Q1bound)
        (by norm_num : 3 ≤ 3) hε
        hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
        hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three direct-height upper endpoint with the upper mean-margin family
replaced by the asymptotic scaled deficit from the Catalan center.

Instead of asking for every `D` to be matched by an upper margin `E / d`, this
route asks for the readable scalar statement
`d * ((1 + 3 * R.lam⁻¹) - upperConcreteModelMeanSeq R 3 d) -> +∞`.  The
arbitrary margin family is then supplied by scalar order bookkeeping. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hCatalanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanCatalanMargin_branchEnvelopeDominations_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    hCatalanError hThreeCatalanAtRatio hMomentSecond
    (upperConcreteModelMeanThreeCatalanUpperMarginFor_of_scaledDeficitTendsToTop
      R hUpperMeanDeficit)
    hUpperExp M hM hLowerWord
    hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three direct-height upper endpoint with the upper mixed side exposed
as the actual deterministic mixed-remainder theorem.

The branch-envelope and scalar case-limit packet is a possible supplier for
this mixed-remainder input, but the canonical instantiation of that packet has
a checked one-quadratic obstruction.  This endpoint therefore records the
clean theorem boundary: prove the upper local mixed remainder directly, and the
upper route does not need to expose the branch scalar packet. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hCatalanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  let errMix : ℝ → ℝ → ℕ → ℝ :=
    fun a slack d => lowerPartialTransposeMixedErrorD 3 (a + slack) M d
  have hLowerMixedFrontier : lowerConcreteMixedErrorFrontier R 3 eps errMix :=
    lowerConcreteMixedErrorFrontier_of_PTPointwiseWordBound
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 3 ≤ 3) hε hM hLowerWord
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_scaledDeficit
      R hThreeCatalanAtRatio hUpperMeanDeficit
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      hCatalanError
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hMomentSecond)
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three direct-height upper endpoint with both mixed sides exposed as
the clean local remainder/frontier theorems.

The lower partial-transpose pointwise word bound is a useful supplier for the
lower mixed frontier, but the upper mechanism only consumes the resulting
`lowerConcreteMixedErrorFrontier`.  This endpoint therefore separates the clean
theorem boundary from one possible PT word-envelope route. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hCatalanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_scaledDeficit
      R hThreeCatalanAtRatio hUpperMeanDeficit
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      hCatalanError
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hMomentSecond)
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three clean endpoint with the geometric input in average-gain
Lemma 4.3 form.

The average-gain statement is converted internally to the direct block-to-`sSup`
form by `lemma43AutoHeightBandsDirectGainSup_of_averageGainSup`; all analytic
inputs remain the clean frontier/remainder inputs used by the upper mechanism. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (hCatalanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hMomentSecond :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    R hε
    (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands.raw)
    hCatalanError hThreeCatalanAtRatio hMomentSecond
    hUpperMeanDeficit hUpperExp hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the deleted-background moment input in
paper-facing variance form.

The endpoint no longer asks for the Chebyshev/Wick deviation-tail predicate
directly.  It consumes the variance theorem
`deletedColumnSphericalMoment_variance_le_const_div_d4 R 3` and derives the
deviation-tail frontier internally by the existing Chebyshev adapter. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (hCatalanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBands hCatalanError hThreeCatalanAtRatio
    (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R 3 hVariance)
    hUpperMeanDeficit hUpperExp hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the two Catalan mean-side inputs supplied
by one explicit finite-diagram estimate.

The endpoint no longer asks separately for the generic Catalan-error frontier
and the length-three balanced-ratio `D / d` estimate.  Both are derived from
the same ratio-parametric diagram bound, which is the actual combinatorial
mean calculation left to prove. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_catalanError_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBands
    (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
      R.sample 3 m Wcard Cmodel hExplicitCatalan)
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
      R
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
        R.sample m Wcard Cmodel hExplicitCatalan))
    hVariance hUpperMeanDeficit hUpperExp hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the upper full-model concentration input
unpacked as the actual exponential tail estimate.

The endpoint no longer hides the upper concentration leaf behind the named
package `UpperConcreteModelMomentExponentialDeviationSetBound`.  It asks
directly for a positive exponent `cUpper` and the eventual bound
`exp (-cUpper d^2)` for the full-model centered background moment deviation
set at every fixed positive slack. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontier_k3
    R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hVariance hUpperMeanDeficit
    ⟨cUpper, hcUpper, by
      intro slack hslack
      filter_upwards [hUpperExpTail slack hslack] with d hd
      simpa [upperConcreteModelExponentialMomentEnvelope] using hd⟩
    hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the upper mean input stated as the signed
Catalan margin actually used by the centering comparison.

This is weaker and more direct than the divergent scaled-deficit input: after
the deleted-column Catalan estimate supplies some `D / d` error, the upper
full-model mean only needs to lie below the same Catalan center by `E / d` for
some `E >= D`. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontier_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedFrontier :
      lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_upperMargin
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R
        (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
          R.sample m Wcard Cmodel hExplicitCatalan))
      hUpperMeanMargin
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε
      (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup
        hLemma43AutoHeightBands.raw)
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample 3 m Wcard Cmodel hExplicitCatalan)
      hLowerMixedFrontier
      hVariance
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      ⟨hcUpper, by
        intro slack hslack
        filter_upwards [hUpperExpTail slack hslack] with d hd
        simpa [upperConcreteModelExponentialMomentEnvelope] using hd⟩
      hUpperMixed

/-- Length-three clean endpoint with the lower mixed frontier stated
existentially.

The upper mechanism only needs some lower mixed-error function whose envelope
and eventual smallness hold.  Its particular closed form is not part of the
upper-rate statement, so this wrapper removes the theorem-facing `errMix`
parameter. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  exact
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
      hVariance hcUpper hUpperExpTail
      (upperConcreteModelMeanThreeCatalanUpperMarginFor_of_scaledDeficitTendsToTop
        R hUpperMeanDeficit)
      hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with existential lower mixed frontier and the
upper mean stated as the signed Catalan margin actually needed.

Compared with the scaled-deficit endpoint, this version does not ask the upper
mean deficit multiplied by `d` to diverge.  It asks only for enough signed
`1 / d` room to dominate the deleted-column Catalan error constant. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  exact
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
      hVariance hcUpper hUpperExpTail hUpperMeanMargin
      hLowerMixedFrontier hUpperMixed

/-- At the clean upper boundary, the variance-tail input is exactly the grouped
second-moment Wick/Chebyshev frontier.

This is not a mathlib-only scalar obligation: the scalar Chebyshev bookkeeping
has already been packaged.  The remaining theorem-strength content is the
two-trace deleted-background second-moment estimate. -/
theorem upper_clean_varianceTail_input_iff_secondMomentWickDeviationTail_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime) :
    deletedColumnSphericalMoment_variance_le_const_div_d4 R 3 ↔
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3 :=
  deletedColumnSphericalMoment_variance_le_const_div_d4_iff_secondMomentWickDeviationTailBound
    R 3

/-- Length-three clean endpoint with the deleted-background input stated as the
grouped second-moment Wick/Chebyshev tail.

This wrapper keeps the theorem boundary closer to the actual proof task:
proving the two-trace second-moment estimate.  The paper-facing variance name
is reconstructed internally. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
      R 3 hSecondMoment)
    hcUpper hUpperExpTail hUpperMeanMargin hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the full-model upper concentration stated
as the existing exponential deviation package.

This wrapper removes a raw pair of inputs from the theorem boundary: the
positive exponent and the displayed tail inequality are exactly the two fields
of `UpperConcreteModelMomentExponentialDeviationSetBound`.  The remaining
mathematical task is the model-specific exponential concentration estimate
itself. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hSecondMoment hUpperExp.1 hUpperExp.2
    hUpperMeanMargin hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the geometric input stated in direct
height-band form.

The average-gain height-band package is not needed at this boundary: the lower
column pipeline consumes the direct block-to-`sSup` form.  Full spherical
isoperimetry for the upper tail is then supplied internally from this direct
height-band input together with the existing cap-cone flattening-map tail. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentration_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  have hMeanCompare : upperLowerConcreteMeanCompare R 3 :=
    upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_upperMargin
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R
        (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
          R.sample m Wcard Cmodel hExplicitCatalan))
      hUpperMeanMargin
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
        R.sample 3 m Wcard Cmodel hExplicitCatalan)
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hSecondMoment)
      (upperLowerConcreteMeanCompare.raw hMeanCompare)
      hUpperExp hUpperMixed

/-- Length-three clean endpoint with the lower Catalan mean input stated as the
direct balanced-ratio `D / d` estimate.

The explicit finite-diagram bound is one possible supplier of this input, but
the upper/lower bridge itself only needs the direct length-three estimate
\[
  |m_{\mathrm{del}}(d) - (1+3\lambda^{-1})| \le D/d.
\]
Together with the signed upper mean margin, this is exactly the mean-side
comparison needed by the upper mechanism. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_threeCatalanDOverD_secondMomentWickTail_upperExponentialConcentration_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMeanMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_threeCatalanDOverD_atBalancedRatio
        R hThreeCatalan)
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hSecondMoment)
      (upperLowerConcreteMeanCompare.raw
        (upperLowerConcreteMeanCompare_three_of_lowerDOverD_and_upperMargin
          R hThreeCatalan hUpperMeanMargin))
      hUpperExp hUpperMixed

/-- Length-three clean endpoint with the whole mean-side comparison compressed
to the signed Catalan-gap packet.

This is the cleanest current centering frontier: the deleted-column mean is
within `D / d` of the Catalan center, and the upper full-model mean sits below
that same center by `E / d` with `D <= E`.  From this one packet the proof
recovers both the lower Catalan-error input and the target mean comparison. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixedFrontier with ⟨errMix, hLowerMixedFrontier⟩
  have hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R :=
    lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_signedCatalanGap
      R hSignedGap
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_lowerMixedErrorFrontier
      R (by norm_num : 3 ≤ 3) hε hLemma43AutoHeightBandsDirectGainSup
      (lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_threeCatalanDOverD_atBalancedRatio
        R hThreeCatalan)
      hLowerMixedFrontier
      (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
        R 3 hSecondMoment)
      (upperLowerConcreteMeanCompare.raw
        (upperLowerConcreteMeanCompare_three_of_signedCatalanGap R hSignedGap))
      hUpperExp hUpperMixed

/-- Length-three signed-Catalan-gap endpoint with the geometric input in
average-gain form.

The signed Catalan gap is the current clean mean-side packet.  The only change
from the direct-height endpoint is that average geometry supplies the direct
height-band input internally. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε
    (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    hSignedGap hSecondMoment hUpperExp hLowerMixedFrontier hUpperMixed

/-- Length-three clean endpoint with the upper mixed remainder split into
branch word bounds and branch scalar limits.

This is the deterministic local-expansion frontier behind the broad
`UpperConcreteModelMixedRemainderBound`: one-linear, one-quadratic, and
multi-defect word estimates, plus the matching scalar limits that make the
finite mixed envelope vanish. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedCaseBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound
        R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound
        R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound
        R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap hSecondMoment
    hUpperExp hLowerMixedFrontier
    (UpperConcreteModelMixedRemainderBound_of_caseMixedWordBounds_and_caseTermLimits
      (R := R) (eps := eps) (k := 3)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (by norm_num : 1 ≤ 3)
      hUpperOneLinearWord hUpperOneQuadraticWord hUpperMultiWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Length-three signed-Catalan-gap endpoint with branch word bounds and
average-gain geometry.

This is the branch-word version of the average-geometry adapter: direct
height-band geometry is supplied internally, while the three mixed word bounds
and their scalar limits remain theorem-facing. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedCaseBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound
        R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound
        R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound
        R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedCaseBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε
    (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    hSignedGap hSecondMoment hUpperExp hLowerMixedFrontier
    hUpperOneLinearWord hUpperOneQuadraticWord hUpperMultiWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three clean endpoint with upper mixed branch envelope dominations
and branch scalar limits.

This is one layer closer to the concrete matrix estimates: the local
one-linear, one-quadratic, and multi-defect word bounds are obtained from
branch envelope dominations, while the scalar branch limits remain explicit. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedBranchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination
        R eps 3 Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
        R eps 3 Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
        R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedCaseBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap hSecondMoment
    hUpperExp hLowerMixedFrontier
    (UpperConcreteModelOneLinearMixedWordBound_of_envelopeDomination
      R (by norm_num : 3 ≤ 3) hε hUpperOneLinearDom)
    (UpperConcreteModelOneQuadraticMixedWordBound_of_envelopeDomination
      R (by norm_num : 3 ≤ 3) hε hUpperOneQuadraticDom)
    (UpperConcreteModelMultiDefectMixedWordBound_of_envelopeDomination
      R (by norm_num : 3 ≤ 3) hε hUpperMultiDom)
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three signed-Catalan-gap endpoint with branch envelope dominations
and average-gain geometry.

This removes the direct height-band geometry input from the scalar-envelope
branch route.  The branch dominations and branch limits remain visible because
they are the actual upper mixed-word suppliers on this route. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedBranchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hLowerMixedFrontier :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination
        R eps 3 Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
        R eps 3 Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
        R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedBranchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
    R hε
    (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    hSignedGap hSecondMoment hUpperExp hLowerMixedFrontier
    hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Length-three clean endpoint with the lower mixed frontier supplied by the
two partial-transpose scale comparisons.

The existential lower mixed frontier is proved internally from the one-`Q` and
many-`Q` PT scale comparisons.  This exposes the actual lower mixed leaves
instead of asking for the packaged frontier as an input. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerPTScaleComparisons_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps M)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hVariance hcUpper hUpperExpTail hUpperMeanDeficit
    (exists_lowerConcreteMixedErrorFrontier_of_PTScaleComparisons
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 3 ≤ 3) hε hM hOneScale hManyScale)
    hUpperMixed

/-- Length-three clean endpoint with the lower mixed frontier supplied by the
two direct partial-transpose scalar estimates.

This is the live companion to the scale-comparison endpoint above.  The
existential lower mixed frontier is assembled internally from the one-`Q` and
many-`Q` direct scalar PT leaves, avoiding the fixed-budget scale-comparison
package that is diagnosed below as inconsistent at length three. -/
theorem
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      finRealSphereAutoHeightBandsAverageGainSup)
    (m Wcard : ℕ) (Cmodel : ℝ)
    (hExplicitCatalan :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (M : ℝ) (hM : 0 ≤ M)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands m Wcard Cmodel hExplicitCatalan
    hVariance hcUpper hUpperExpTail hUpperMeanDeficit
    (exists_lowerConcreteMixedErrorFrontier_of_PTDirectScalarCases
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 3 ≤ 3) hε hM hOne hMany)
    hUpperMixed

/-- The fixed-budget lower PT scale-comparison supplier for the clean endpoint
is inconsistent at length three.

The endpoint above exposes the pair
`lowerConcretePTMixedWordOneQScaleComparison R 3 eps M` and
`lowerConcretePTMixedWordManyQScaleComparison R 3 eps M` with `0 <= M`.
The lower-side no-go theorem rules out exactly this pair, so this supplier route
is diagnostic rather than a theorem still waiting to be proved. -/
theorem
    upper_clean_lowerPTScaleComparison_supplier_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (M : ℝ) (hM : 0 ≤ M)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps M) :
    False :=
  lowerConcretePTMixedWordScaleComparisons_three_not_uniform
    (R := R) (ε := eps) hε M hM ⟨hOneScale, hManyScale⟩

/-- The newest clean scale-comparison supplier is inconsistent even without a
separate nonnegativity hypothesis on `M`.

The many-`Q` scale comparison already forces `M >= 0`, and then the fixed-`M`
scale-comparison no-go applies. -/
theorem
    upper_clean_lowerPTScaleComparison_supplier_impossible_noM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps M : ℝ} (hε : 0 < eps)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps M)
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps M) :
    False :=
  upper_clean_lowerPTScaleComparison_supplier_impossible_k3
    (R := R) (eps := eps) hε M
    (lowerConcretePTMixedWordManyQScaleComparison_nonneg_M
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num) hε hManyScale)
    hOneScale hManyScale

/-- The runtime-native lower mixed-error witness cannot supply the clean
existential lower mixed frontier at length three.

The clean endpoint only asks for some `errMix` with a sphere-supported mixed
envelope and eventual smallness.  The current runtime-native envelope supplies
the deterministic word control, but its associated finite error is not `o(1)`.
Thus `errMix = lowerConcreteMixedRuntimeWordError R 3` is a diagnosed failed
supplier, not a remaining theorem to prove. -/
theorem
    upper_clean_lowerRuntimeMixedError_supplier_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps) :
    ¬ lowerConcreteMixedErrorFrontier R 3 eps
      (lowerConcreteMixedRuntimeWordError R 3) :=
  lowerConcreteMixedRuntimeWordError_three_not_mixedErrorFrontier
    (R := R) (ε := eps) hε

/-- The one-quadratic scalar input on the newest branch-envelope upper route
cannot be supplied by a canonical domination package at length three.

This is the checked obstruction behind the scalar frontier: domination of the
actual-model canonical one-quadratic term together with a zero-limit scalar
package would force a divergent term to be eventually below a term tending to
zero. -/
theorem
    upper_concrete_directHeight_endpoint_oneQuadratic_scalar_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound Q1bound : ℝ → ℕ → ℝ} :
    ¬ (UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
          R eps 3 Abound Q1bound ∧
        UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound) :=
  upperConcreteModel_oneQuadraticDom_and_termLimit_impossible R hε

/-- The scalar upper mixed packet on the newest branch-envelope upper route is
inconsistent whenever it is instantiated by canonical-style dominations for
all three branches.

The proof uses only the one-quadratic obstruction, so this diagnostic is
deliberately sharper than a generic "some input is missing" statement. -/
theorem
    upper_concrete_directHeight_endpoint_branchEnvelope_caseTerm_packet_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ} :
    ¬ (UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
          Abound L1bound ∧
        UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
          Abound Q1bound ∧
        UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
          Abound L2bound Q2bound ∧
        UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound ∧
        UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound ∧
        UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) := by
  intro h
  exact
    upperConcreteModel_oneQuadraticDom_and_termLimit_impossible
      R hε ⟨h.2.1, h.2.2.2.2.1⟩

/-- Length-three upper endpoint with the Catalan side stated only at the actual
balanced aspect ratio `R.lam`.

Compared with the preceding wrapper, this removes the ratio-parametric
quantifier from the article-facing Catalan input.  The remaining mean-side
input is the direct statement that the deleted-column third moment is
eventually within `D / d` of `1 + 3 * R.lam⁻¹`; the upper full-model moment
tail is now consumed through the named exponential concentration proposition
instead of an unfolded set-probability bound.  On the upper mixed-word side,
all three deterministic branch estimates are supplied by local matrix
estimates plus scalar envelope-domination inputs; the three scalar
branch-limit packages remain visible. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound n
                                    tauSep
                                    (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                        n pole a tauBand))
                                    (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                      Cmodel A
                                      (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                        n pole a tauBand))
                                    (sSup
                                      (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                        n r A)))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases
    lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
      R.sample
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_atBalancedRatio
        R hThreeCatalan) with
    ⟨Cmodel, hExplicitCatalan⟩
  have hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 :=
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
      R.sample 3 0 1 Cmodel hExplicitCatalan
  have hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3 :=
    UpperConcreteModelMixedRemainderBound_of_branchEnvelopeDominations_and_caseTermLimits
      (R := R) (eps := eps) (k := 3)
      (Abound := Abound) (L2bound := L2bound) (L1bound := L1bound)
      (Q2bound := Q2bound) (Q1bound := Q1bound)
      (by norm_num) hε
      hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R (by norm_num) hε hLemma43AutoHeightBandsDirectGainSup
      hMeanError (M := max M 0) (le_max_right M 0)
      hOne hMany hVariance
      (by simpa [upperConcreteModelMeanSeq] using hMeanCompare)
      hUpperExp hUpperMixed

/-- Average-form direct-PT-scalar endpoint with the upper mixed input kept as
the honest model-level mixed-remainder predicate.

The older branch-domination/branch-limit wrapper below is useful diagnostically,
but its upper mixed branch package is inconsistent at `k = 3`.  This wrapper
therefore exposes `UpperConcreteModelMixedRemainderBound R eps 3` directly. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases
    lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio_of_threeCatalanDOverD
      R.sample
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_atBalancedRatio
        R hThreeCatalan) with
    ⟨Cmodel, hExplicitCatalan⟩
  have hMeanError :
      lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio R.sample 3 :=
    lowerDeletedColumnBackgroundMomentCatalanErrorBound_fromRatio_of_explicitDiagramBound
      R.sample 3 0 1 Cmodel hExplicitCatalan
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanError_varianceStack_meanCompare_exponentialDeviationSetBound_mixedRemainder_ptDirectScalarCases
      R (by norm_num) hε
      (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup hLemma43AutoHeightBands)
      hMeanError (M := max M 0) (le_max_right M 0)
      hOne hMany hVariance
      (by simpa [upperConcreteModelMeanSeq] using hMeanCompare)
      hUpperExp hUpperMixed

/-- Named-input mixed-remainder endpoint with the lower background variance stack
supplied by the stronger deleted-background exponential tail source.

This is the current non-vacuous upper route: the refuted scalar-branch package is
not used.  The remaining upper local-spike input is the honest model-level
`UpperConcreteModelMixedRemainderBound R eps 3`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hLowerExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands.raw hThreeCatalan M hOne hMany
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
      R 3 hLowerExpTail)
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hUpperExp hUpperMixed

/-- Named-input mixed-remainder endpoint with the lower Catalan input stated in
the stronger ratio-parametric `D / d` form.

This removes the balanced-ratio Catalan adapter from the theorem-facing
frontier.  The remaining mean-side theorem-strength input is the
ratio-parametric deleted-column Wick/Catalan error estimate itself. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hLowerExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
      R hThreeCatalan)
    M hOne hMany hLowerExpTail hMeanCompare hUpperExp hUpperMixed

/-- Ratio-parametric Catalan endpoint with the broad upper mixed remainder
split into deterministic word bounds and scalar envelope limits.

This is the sharpest current non-vacuous local-spike interface on the ratio
Catalan route.  The caller may choose any envelopes that satisfy both the
finite-word bound and the finite-sum scalar decay; the refuted canonical
envelopes are not assumed here. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hLowerExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hLowerExpTail
    hMeanCompare hUpperExp
    (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
      R (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Ratio-parametric Catalan endpoint with the lower background side stated at
the variance/Chebyshev level.

The stronger deleted-background exponential tail is not needed for this upper
assembly step.  This wrapper exposes the weaker paper-facing variance input
directly, while keeping the upper local-spike input in its honest broad
mixed-remainder form. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
      R hThreeCatalan)
    M hOne hMany hVariance (upperLowerConcreteMeanCompare.raw hMeanCompare)
    hUpperExp hUpperMixed

/-- Ratio-parametric Catalan variance-stack endpoint with the upper mixed input
split into deterministic word bounds and scalar envelope limits.

This is the current sharp non-vacuous upper route: it keeps only the weaker
lower variance/Chebyshev input and exposes the upper local-spike work as
word-bound plus scalar-decay obligations. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hVariance
    hMeanCompare hUpperExp
    (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
      R (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Ratio-parametric Catalan variance-stack endpoint with the mean comparison
supplied by the signed Catalan gap.

This keeps the sharp word-bound plus scalar-decay upper mixed interface, but
replaces the black-box mean comparison by the concrete signed estimate: the
deleted-column mean is within `D / d` of the Catalan center, and the upper
full-model mean is below the same center by at least `E / d` with `D <= E`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hVariance
    (upperLowerConcreteMeanCompare_three_of_signedCatalanGap R hSignedGap)
    hUpperExp hUpperWord hUpperTerm

/-- Ratio-parametric signed-gap endpoint with the upper concentration input
stated as existence of some exponential rate.

The proof never uses the numerical name of `cUpper`; it only needs a valid
exponential concentration packet for some rate.  This wrapper removes that
inessential witness from the theorem-facing interface. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
      R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hVariance
      hSignedGap hUpperExp hUpperWord hUpperTerm

/-- Ratio-parametric signed-gap endpoint with the lower PT budget made
existential.

The upper mechanism does not use the numerical value of the PT scalar budget.
It only needs some nonnegative budget for which the one-`Q` and many-`Q` direct
scalar estimates hold. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerPT with ⟨M, hM, hOne, hMany⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
      R hε hLemma43AutoHeightBands hThreeCatalan M
      (by simpa [max_eq_left hM] using hOne)
      (by simpa [max_eq_left hM] using hMany)
      hVariance hSignedGap hUpperExp hUpperWord hUpperTerm

/-- Ratio-parametric signed-gap endpoint with the upper mixed envelopes made
existential.

The upper mechanism does not use the names of the five envelope functions.  It
only needs some envelope packet for which the model-level word bound and the
scalar term limit both hold. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_upperMixedEnvelopeExists_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteModelMixedTermLimit 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperMixed with
    ⟨Abound, L2bound, L1bound, Q2bound, Q1bound, hUpperWord, hUpperTerm⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCasesExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalan hLowerPT hVariance hSignedGap
      hUpperExp hUpperWord hUpperTerm

/-- Ratio-parametric signed-gap endpoint with the deleted-background variance
input stated as the grouped second-moment/Wick deviation tail.

At this abstraction layer the paper-facing variance name is supplied by the
same Wick/Chebyshev tail frontier.  This wrapper exposes that frontier directly
on the current cleaned endpoint. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_secondMomentWickTail_upperExponentialConcentrationExists_signedCatalanGap_upperMixedEnvelopeExists_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound
        R 3)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteModelMixedTermLimit 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_upperMixedEnvelopeExists_lowerPTDirectScalarCasesExists_k3
    R hε hLemma43AutoHeightBands hThreeCatalan hLowerPT
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_secondMomentWickDeviationTailBound
      R 3 hSecondMoment)
    hSignedGap hUpperExp hUpperMixed

/-- Ratio-parametric cleaned endpoint with the signed mean-gap packet supplied
from the lower `D / d` Catalan estimate and a divergent upper scaled deficit.

The signed gap is not an independent wrapper here: the lower side is the
ratio-parametric three-Catalan estimate already present in the endpoint, while
the upper side is the explicit one-sided deficit
`d * (CatalanCenter - upperMean d) -> +∞`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedEnvelopeExists_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound
        R 3)
    (hUpperDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteModelMixedTermLimit 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_secondMomentWickTail_upperExponentialConcentrationExists_signedCatalanGap_upperMixedEnvelopeExists_lowerPTDirectScalarCasesExists_k3
    R hε hLemma43AutoHeightBands hThreeCatalan hLowerPT hSecondMoment
    (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_scaledDeficit
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R hThreeCatalan)
      hUpperDeficit)
    hUpperExp hUpperMixed

/-- Cleaned ratio-parametric endpoint with the upper mixed scalar input split
into its three envelope branches.

The previous wrapper asked for one packaged mixed-term limit.  This version
keeps the same deterministic model-level word estimate, but exposes the scalar
asymptotic work in the branch structure used by the envelope definition:
one-linear defect, one-quadratic defect, and the remaining multi-defect words.
This is the useful theorem-facing frontier because the canonical length-three
route is known to fail on the one-quadratic and multi-defect scalar branches. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedWordBound_defectCaseLimits_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound
        R 3)
    (hUpperDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteMixedDefectCaseLimits 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperMixed with
    ⟨Abound, L2bound, L1bound, Q2bound, Q1bound, hUpperWord,
      hDefectLimits⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedEnvelopeExists_lowerPTDirectScalarCasesExists_k3
      R hε hLemma43AutoHeightBands hThreeCatalan hLowerPT hSecondMoment
      hUpperDeficit hUpperExp
      ⟨Abound, L2bound, L1bound, Q2bound, Q1bound, hUpperWord,
        UpperConcreteModelMixedTermLimit_of_defectCaseLimits hDefectLimits⟩

/-- Cleaned endpoint with the lower length-three Catalan input supplied by an
explicit finite-diagram estimate.

The endpoint no longer asks directly for
`lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio R.sample`.
Instead it consumes a concrete diagram bound at `k = 3`; the adapter
`lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound`
turns that into the required uniform `D / d` Catalan estimate. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedWordBound_defectCaseLimits_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    {m Wcard : ℕ} {Cmodel : ℝ}
    (hCatalanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound
        R 3)
    (hUpperDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteMixedDefectCaseLimits 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_secondMomentWickTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedWordBound_defectCaseLimits_lowerPTDirectScalarCasesExists_k3
    R hε hLemma43AutoHeightBands
    (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
      R.sample m Wcard Cmodel hCatalanDiagram)
    hLowerPT hSecondMoment hUpperDeficit hUpperExp hUpperMixed

/-- Cleaned endpoint with the lower background fluctuation input stated as the
paper-facing variance/Chebyshev estimate.

The previous cleaned diagram endpoint consumed the grouped
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound`.  This
version consumes `deletedColumnSphericalMoment_variance_le_const_div_d4`
instead and applies the existing Chebyshev adapter internally. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedWordBound_defectCaseLimits_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    {m Wcard : ℕ} {Cmodel : ℝ}
    (hCatalanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteMixedDefectCaseLimits 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_secondMomentWickTail_upperExponentialConcentrationExists_upperScaledDeficit_upperMixedWordBound_defectCaseLimits_lowerPTDirectScalarCasesExists_k3
    R hε hLemma43AutoHeightBands hCatalanDiagram hLowerPT
    (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R 3 hVariance)
    hUpperDeficit hUpperExp hUpperMixed

/-- Cleaned endpoint with the upper mean input stated as the direct Catalan
margin used by the proof.

The stronger scaled-deficit input is no longer needed at the theorem surface.
It is enough to know that every lower deleted-column `D / d` Catalan error can
be matched by an upper full-model `E / d` gap with `D <= E`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedWordBound_defectCaseLimits_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    {m Wcard : ℕ} {Cmodel : ℝ}
    (hCatalanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
        UpperConcreteModelMixedWordBound R eps 3
            Abound L2bound L1bound Q2bound Q1bound ∧
          UpperConcreteMixedDefectCaseLimits 3
            Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperMixed with
    ⟨Abound, L2bound, L1bound, Q2bound, Q1bound, hUpperWord,
      hDefectLimits⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentrationExists_signedCatalanGap_modelMixedWordBound_termLimit_lowerPTDirectScalarCasesExists_k3
      R hε hLemma43AutoHeightBands
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
        R.sample m Wcard Cmodel hCatalanDiagram)
      hLowerPT hVariance
      (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_upperMargin
        R
        (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
          R
          (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
            R.sample m Wcard Cmodel hCatalanDiagram))
        hUpperMargin)
      hUpperExp hUpperWord
      (UpperConcreteModelMixedTermLimit_of_defectCaseLimits hDefectLimits)

/-- Cleaned endpoint with the local spike input stated as the broad mixed
remainder estimate.

This is the direct mathematical interface for the upper local-spike part:
after the Catalan, variance, mean-margin, lower-PT, and concentration inputs
are supplied, the proof only needs the statement that all upper mixed words are
absorbed into an `o(1)` remainder.  Branch envelopes and scalar term limits are
one possible way to prove this input, but they are not part of the cleanest
theorem surface. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_mixedRemainder_lowerPTDirectScalarCasesExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    {m Wcard : ℕ} {Cmodel : ℝ}
    (hCatalanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerPT :
      ∃ M : ℝ,
        0 ≤ M ∧
          lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M ∧
            lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerPT with ⟨M, hM, hOne, hMany⟩
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  have hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample :=
    lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio_of_explicitDiagramBound
      R.sample m Wcard Cmodel hCatalanDiagram
  have hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R :=
    upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_upperMargin
      R
      (lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio_of_fromRatio
        R hThreeCatalan)
      hUpperMargin
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
      R hε hLemma43AutoHeightBands hThreeCatalan M
      (by simpa [max_eq_left hM] using hOne)
      (by simpa [max_eq_left hM] using hMany)
      hVariance
      (upperLowerConcreteMeanCompare_three_of_signedCatalanGap R hSignedGap)
      hUpperExp hUpperMixed

/-- Cleaned endpoint with the lower local-spike input stated as the broad
mixed-error frontier.

The one-`Q` and many-`Q` partial-transpose scalar estimates are one useful
supplier for this frontier, but the upper-bound mechanism only consumes the
resulting lower mixed envelope and its eventual smallness. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    {m Wcard : ℕ} {Cmodel : ℝ}
    (hCatalanDiagram :
      lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
        R.sample 3 m Wcard Cmodel)
    (hLowerMixed :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hLowerMixed with ⟨errMix, hLowerMixed⟩
  rcases hUpperExp with ⟨cUpper, hcUpper, hUpperExpTail⟩
  exact
    upper_eventual_from_concrete_model_of_averageHeightBands_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialTail_upperMeanCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontier_k3
      R hε hLemma43AutoHeightBands m Wcard Cmodel hCatalanDiagram
      hVariance hcUpper
      (by
        intro slack hslack
        filter_upwards [hUpperExpTail slack hslack] with d hd
        simpa [upperConcreteModelExponentialMomentEnvelope] using hd)
      hUpperMargin hLowerMixed hUpperMixed

/-- Cleaned endpoint with the Catalan finite-diagram input stated
existentially.

The particular finite diagram parameters are bookkeeping for the deleted-column
moment computation.  The upper mechanism only needs that some explicit diagram
bound exists at length three. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanDiagramExists_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hCatalanDiagram :
      ∃ m Wcard : ℕ, ∃ Cmodel : ℝ,
        lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
          R.sample 3 m Wcard Cmodel)
    (hLowerMixed :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixed :
      UpperConcreteModelMixedRemainderBound R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hCatalanDiagram with ⟨m, Wcard, Cmodel, hCatalanDiagram⟩
  exact
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_explicitCatalanDiagramBound_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBands hCatalanDiagram hLowerMixed hVariance
      hUpperMargin hUpperExp hUpperMixed

/-- Certified finite mixed-word checklist for the actual upper local spike.

This is the Lean counterpart of replacing a vague "mixed words are small"
sentence by a finite verification problem: choose envelope functions, prove the
word-by-word mixed estimate, and prove the scalar envelope tends to zero for
each mixed word. -/
def UpperConcreteCertifiedMixedWordChecklist
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : Prop :=
  ∃ Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ,
    UpperConcreteModelMixedWordBound R eps k
        Abound L2bound L1bound Q2bound Q1bound ∧
      UpperConcreteModelMixedTermLimit k
        Abound L2bound L1bound Q2bound Q1bound

/-- The certified finite mixed-word checklist supplies the broad mixed
remainder input. -/
theorem UpperConcreteCertifiedMixedWordChecklist.to_mixedRemainder
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps k) :
    UpperConcreteModelMixedRemainderBound R eps k := by
  rcases hChecklist with
    ⟨Abound, L2bound, L1bound, Q2bound, Q1bound, hWord, hLimit⟩
  exact
    UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
      R hk hWord hLimit

/-- Cleaned endpoint with the upper local spike input stated as a certified
finite mixed-word checklist.

This is the explicit-word version of the mixed-remainder endpoint: proving the
finite checklist is exactly one way to discharge the upper local mixed
remainder without hiding the mixed words. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanDiagramExists_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedChecklist_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hCatalanDiagram :
      ∃ m Wcard : ℕ, ∃ Cmodel : ℝ,
        lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
          R.sample 3 m Wcard Cmodel)
    (hLowerMixed :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMargin :
      ∀ D : ℝ, 0 ≤ D →
        upperConcreteModelMeanThreeCatalanUpperMarginFor R D)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanDiagramExists_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hCatalanDiagram hLowerMixed hVariance
    hUpperMargin hUpperExp
    (UpperConcreteCertifiedMixedWordChecklist.to_mixedRemainder
      R (by norm_num : 1 ≤ 3) hUpperMixedChecklist)

/-- Cleaned endpoint with the upper mean side stated as a scaled Catalan
deficit.

This replaces the margin family
`forall D >= 0, upperConcreteModelMeanThreeCatalanUpperMarginFor R D` by the
single scalar asymptotic statement
`d * ((1 + 3 / lambda) - m_upper(d)) -> +infty`.  The conversion from the
scaled deficit to arbitrary `E / d` margins is scalar order bookkeeping. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanDiagramExists_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedChecklist_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hCatalanDiagram :
      ∃ m Wcard : ℕ, ∃ Cmodel : ℝ,
        lowerDeletedColumnBackgroundMomentExplicitCatalanDiagramBound_fromRatio
          R.sample 3 m Wcard Cmodel)
    (hLowerMixed :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_catalanDiagramExists_varianceTail_upperExponentialConcentrationExists_upperCatalanMargin_upperMixedChecklist_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hCatalanDiagram hLowerMixed hVariance
    (upperConcreteModelMeanThreeCatalanUpperMarginFor_of_scaledDeficitTendsToTop
      R hUpperMeanDeficit)
    hUpperExp hUpperMixedChecklist

/-- Cleaned endpoint with the lower Catalan side stated directly as the
length-three `D / d` estimate.

This removes the finite Catalan-diagram witnesses from the theorem-facing
route.  The lower mean input is now exactly the scalar estimate around
`1 + 3 * lambda^-1`; diagram bounds remain one possible supplier, not the
endpoint surface. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedChecklist_lowerMixedErrorFrontierExists_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixed :
      ∃ errMix : ℝ → ℝ → ℕ → ℝ,
        lowerConcreteMixedErrorFrontier R 3 eps errMix)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
    R hε hLemma43AutoHeightBands hThreeCatalanAtRatio hLowerMixed hVariance
    hUpperMeanDeficit hUpperExp
    (UpperConcreteCertifiedMixedWordChecklist.to_mixedRemainder
      R (by norm_num : 1 ≤ 3) hUpperMixedChecklist)

/-- Certified finite mixed-word checklist for the lower local spike.

This is the lower-side counterpart of the upper checklist: choose a
word-by-word envelope, prove the finite word budget, and prove that the same
error sequence tends to zero.  The checklist is exactly the explicit route to
the packaged lower mixed frontier. -/
def LowerConcreteCertifiedMixedWordChecklist
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (eps : ℝ) (k : ℕ) : Prop :=
  ∃ bound : ℝ → ℝ → ℕ → (Fin k → LocalExpansionLetter) → ℝ,
    ∃ errMix : ℝ → ℝ → ℕ → ℝ,
      lowerConcreteMixedWordPointwiseBoundOnSphere R k eps bound ∧
        lowerConcreteMixedWordBudgetWithError R k eps bound errMix ∧
          lowerConcreteMixedErrorEventuallySmall k eps errMix

/-- The lower certified finite mixed-word checklist supplies the existential
mixed frontier consumed by the upper/lower bridge. -/
theorem LowerConcreteCertifiedMixedWordChecklist.to_exists_mixedFrontier
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps k) :
    ∃ errMix : ℝ → ℝ → ℕ → ℝ,
      lowerConcreteMixedErrorFrontier R k eps errMix := by
  rcases hChecklist with
    ⟨bound, errMix, hWord, hBudget, hSmall⟩
  exact
    ⟨errMix,
      lowerConcreteMixedErrorFrontier_of_wordBoundsAndBudget
        R hk bound errMix hWord hBudget hSmall⟩

/-- Direct-height-band checklist endpoint with the mean side compressed to one
signed Catalan-gap packet.

This endpoint also exposes the background typicality side as the exact
two-trace Wick/Chebyshev frontier, rather than the paper-facing variance alias.
The variance-named wrapper below is just an adapter to this theorem. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedChecklist_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  exact
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedRemainder_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap hSecondMoment
      hUpperExp
      (LowerConcreteCertifiedMixedWordChecklist.to_exists_mixedFrontier
        R (by norm_num : 1 ≤ 3) hLowerMixedChecklist)
      (UpperConcreteCertifiedMixedWordChecklist.to_mixedRemainder
        R (by norm_num : 1 ≤ 3) hUpperMixedChecklist)

/-- Direct-height-band endpoint with the upper mixed side exposed as the three
branch word estimates and the three scalar branch limits.

This is sharper than the certified upper checklist: the theorem surface now
names the one-linear, one-quadratic, and multi-defect word estimates separately,
together with the scalar limits that make those three envelopes vanish. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedCaseBounds_caseTermLimits_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  exact
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedCaseBounds_caseTermLimits_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap hSecondMoment
      hUpperExp
      (LowerConcreteCertifiedMixedWordChecklist.to_exists_mixedFrontier
        R (by norm_num : 1 ≤ 3) hLowerMixedChecklist)
      hUpperOneLinearWord hUpperOneQuadraticWord hUpperMultiWord
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Direct-height-band endpoint with the upper mixed side exposed as branch
envelope dominations and scalar branch limits.

This is one layer closer to the concrete mixed-word estimates than the
case-bound endpoint: each branch word estimate is supplied from its envelope
domination, while the three scalar limits remain explicit. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedBranchEnvelopeDominations_caseTermLimits_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination
        R eps 3 Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination
        R eps 3 Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination
        R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  rcases hUpperExp with ⟨cUpper, hUpperExp⟩
  exact
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentration_upperMixedBranchEnvelopeDominations_caseTermLimits_lowerMixedErrorFrontierExists_k3
      R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap hSecondMoment
      hUpperExp
      (LowerConcreteCertifiedMixedWordChecklist.to_exists_mixedFrontier
        R (by norm_num : 1 ≤ 3) hLowerMixedChecklist)
      hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Direct-height-band endpoint with the canonical actual-model upper word
bounds supplied internally.

The three word estimates are closed by the canonical actual-model branch
suppliers.  The theorem surface therefore contains only the three scalar branch
limits.  At length three those canonical scalar limits are known to be
inconsistent, so this endpoint is diagnostic: it proves that the word-estimate
half is not the obstruction. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedCaseBounds_caseTermLimits_lowerMixedChecklist_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap
    hLowerMixedChecklist hSecondMoment hUpperExp
    (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
      R (by norm_num : 3 ≤ 3) hε)
    (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
      R (by norm_num : 3 ≤ 3) hε)
    (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
      R (by norm_num : 3 ≤ 3) hε)
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- The canonical scalar packet for the cleaned signed-gap/Wick endpoint is
inconsistent at length three.

The canonical word estimates above are available, but the corresponding
canonical scalar limit cannot be true: the one-quadratic branch already
diverges instead of tending to zero. -/
theorem
    upper_concrete_signedGapWick_canonicalWordBounds_endpoint_caseTerm_packet_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    False := by
  let _ := hUpperOneLinearTerm
  let _ := hUpperMultiTerm
  exact
    upperConcreteModel_oneQuadraticMixedTermLimit_not_canonical
      (R := R) hε hUpperOneQuadraticTerm

/-- Signed-gap/Wick endpoint with the lower mixed checklist unpacked into
word-by-word control, finite budget, and scalar smallness.

This removes the lower certified checklist from the theorem surface.  The lower
mixed input is now the exact three-part proof object used to build that
checklist: pointwise mixed-word bounds on the sphere, a finite error budget,
and eventual smallness of the same error sequence. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerMixedWordBoundsBudget_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    {bound : ℝ → ℝ → ℕ → (Fin 3 → LocalExpansionLetter) → ℝ}
    {errMix : ℝ → ℝ → ℕ → ℝ}
    (hLowerMixedWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps bound)
    (hLowerMixedBudget :
      lowerConcreteMixedWordBudgetWithError R 3 eps bound errMix)
    (hLowerMixedSmall :
      lowerConcreteMixedErrorEventuallySmall 3 eps errMix)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerMixedChecklist_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap
    ⟨bound, errMix, hLowerMixedWord, hLowerMixedBudget, hLowerMixedSmall⟩
    hSecondMoment hUpperExp
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Signed-gap/Wick endpoint with the lower mixed side reduced to one
pointwise partial-transpose mixed-word estimate.

The finite PT budget and scalar smallness of the literal PT error are supplied
internally.  The remaining lower mixed theorem-facing input is the pointwise
word estimate on the Frobenius sphere. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerWord :
      lowerConcreteMixedWordPointwiseBoundOnSphere R 3 eps
        (fun a slack d =>
          lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d))
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerMixedWordBoundsBudget_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap
    hLowerWord
    (lowerConcreteMixedWordBudgetWithPTError_literal
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 0 < 3) hε hM)
    (lowerConcreteMixedErrorEventuallySmall_of_lowerPartialTransposeMixedErrorD
      (k := 3) (ε := eps) (M := M) (by norm_num : 3 ≤ 3))
    hSecondMoment hUpperExp
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Signed-gap/Wick endpoint with the lower mixed side reduced to the two
direct partial-transpose scalar cases.

The lower pointwise mixed-word estimate is supplied internally by the
`one-Q`/`many-Q` case split.  Thus the theorem-facing lower mixed leaves are
exactly the two direct scalar trace estimates. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerOneQ :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hLowerManyQ :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTPointwiseMixedWordBound_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap M hM
    (lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
      (R := R) (k := 3) (ε := eps) (M := M)
      (by norm_num : 0 < 3) hε hM hLowerOneQ hLowerManyQ)
    hSecondMoment hUpperExp
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Same signed-gap/Wick endpoint, but with the upper full-model concentration
input unpacked as the actual exponential tail estimate.

The theorem surface no longer hides this leaf behind the existential
`UpperConcreteModelMomentExponentialDeviationSetBound` package.  It asks
directly for a positive exponent and the eventual bound `exp (-c d^2)` for the
full-model centered background moment deviation set at every fixed positive
slack. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialTail_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerOneQ :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hLowerManyQ :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hSecondMoment :
      lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap M hM
    hLowerOneQ hLowerManyQ hSecondMoment
    ⟨cUpper, hcUpper, by
      intro slack hslack
      filter_upwards [hUpperExpTail slack hslack] with d hd
      simpa [upperConcreteModelExponentialMomentEnvelope] using hd⟩
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Same signed-gap/Wick endpoint, with the deleted-background moment tail
supplied from the variance bound used in the Wick second-moment estimate.

The theorem surface no longer asks for the packaged
`lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound`.
It asks directly for the variance estimate
`deletedColumnSphericalMoment_variance_le_const_div_d4 R 3`, which is the
input used by the checked adapter below. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialTail_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerOneQ :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hLowerManyQ :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialTail_canonicalUpperMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap M hM
    hLowerOneQ hLowerManyQ
    (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
      R 3 hVariance)
    hcUpper hUpperExpTail
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Direct-height-band checklist endpoint with the mean side compressed to one
signed Catalan-gap packet.

This is the cleanest current checklist surface: the deleted-column Catalan
error and the upper/lower mean comparison are both recovered from the single
signed gap input.  Thus the endpoint no longer exposes the stronger scaled
upper-deficit sufficient condition when the proof only needs the signed
comparison packet. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_upperMixedChecklist_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_secondMomentWickTail_upperExponentialConcentrationExists_upperMixedChecklist_lowerMixedChecklist_k3
      R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap
      hLowerMixedChecklist
      (lowerConcreteDeletedBackgroundMomentSecondMomentWickDeviationTailBound_of_deletedColumnSphericalMoment_variance_le_const_div_d4
        R 3 hVariance)
      hUpperExp hUpperMixedChecklist

/-- Direct-height-band checklist endpoint with the upper full-model
concentration input unpacked as the literal exponential tail.

This is the same clean finite-checklist route as the previous theorem, but it
does not hide the probability leaf behind the existential
`UpperConcreteModelMomentExponentialDeviationSetBound` package. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialTail_upperMixedChecklist_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_upperMixedChecklist_lowerMixedChecklist_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap
    hLowerMixedChecklist hVariance
    ⟨cUpper, hcUpper, by
      intro slack hslack
      filter_upwards [hUpperExpTail slack hslack] with d hd
      simpa [upperConcreteModelExponentialMomentEnvelope] using hd⟩
    hUpperMixedChecklist

/-- Direct-height-band checklist endpoint with the lower finite checklist
reduced to the two direct partial-transpose scalar mixed-word cases.

The lower pointwise word estimate, finite word budget, and error-smallness
adapter are supplied internally; the remaining lower mixed leaves are the
one-`Q` and many-`Q` scalar trace bounds. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialTail_upperMixedChecklist_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hSignedGap : upperLowerConcreteMeanThreeCatalanSignedGap R)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerOneQ :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hLowerManyQ :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialTail_upperMixedChecklist_lowerMixedChecklist_k3
    R hε hLemma43AutoHeightBandsDirectGainSup hSignedGap
    ⟨fun a slack d => lowerPartialTransposeMixedWordBoundD 3 (a + slack) M d,
      fun a slack d => lowerPartialTransposeMixedErrorD 3 (a + slack) M d,
      lowerConcreteMixedWordPointwiseBoundOnSphere_withPTError_of_directScalarCases
        (R := R) (k := 3) (ε := eps) (M := M)
        (by norm_num : 0 < 3) hε hM hLowerOneQ hLowerManyQ,
      lowerConcreteMixedWordBudgetWithPTError_literal
        (R := R) (k := 3) (ε := eps) (M := M)
        (by norm_num : 0 < 3) hε hM,
      lowerConcreteMixedErrorEventuallySmall_of_lowerPartialTransposeMixedErrorD
        (k := 3) (ε := eps) (M := M) (by norm_num : 3 ≤ 3)⟩
    hVariance hcUpper hUpperExpTail hUpperMixedChecklist

/-- Direct-height-band version of the sharp checklist endpoint.

This is the geometry-minimal form of the current route: the proof only needs
the direct block-to-sup height-band statement.  The average-height-band packet
is a supplier for this input, not part of the clean endpoint surface. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedChecklist_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η := by
  exact
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialConcentrationExists_upperMixedChecklist_lowerMixedChecklist_k3
      R hε hLemma43AutoHeightBandsDirectGainSup
      (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_scaledDeficit
        R hThreeCatalanAtRatio hUpperMeanDeficit)
      hLowerMixedChecklist hVariance hUpperExp hUpperMixedChecklist

/-- Direct-height-band checklist endpoint with the lower mean, variance, upper
concentration, and both local mixed inputs stated without the older exponential
concentration package. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedChecklist_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialTail_upperMixedChecklist_lowerMixedChecklist_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_scaledDeficit
      R hThreeCatalanAtRatio hUpperMeanDeficit)
    hLowerMixedChecklist hVariance hcUpper hUpperExpTail hUpperMixedChecklist

/-- Direct-height-band checklist endpoint with the lower Catalan side compressed
to the balanced-ratio estimate and the lower mixed side reduced to the two
direct partial-transpose scalar cases. -/
theorem
    upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialTail_upperMeanScaledDeficit_upperMixedChecklist_lowerPTDirectScalarCases_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBandsDirectGainSup :
      finRealSphereAutoHeightBandsDirectGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    {cUpper : ℝ}
    (hcUpper : 0 < cUpper)
    (hUpperExpTail :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          (PptFactorization.AppendixB.sphericalModelMeasure
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))).real
            (backgroundMomentDeviationSet
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))
              (upperConcreteN d)
              (upperCanonicalTau slack d)
              (upperConcreteMean
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                3 d)
              3) ≤
            Real.exp (-(cUpper * (d : ℝ) ^ 2)))
    (M : ℝ) (hM : 0 ≤ M)
    (hLowerOneQ :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps M)
    (hLowerManyQ :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps M)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_signedCatalanGap_varianceTail_upperExponentialTail_upperMixedChecklist_lowerPTDirectScalarCases_k3
    R hε hLemma43AutoHeightBandsDirectGainSup
    (upperLowerConcreteMeanThreeCatalanSignedGap_of_lowerDOverD_and_scaledDeficit
      R hThreeCatalanAtRatio hUpperMeanDeficit)
    hVariance hcUpper hUpperExpTail M hM hLowerOneQ hLowerManyQ
    hUpperMixedChecklist

/-- Cleaned endpoint with both local mixed sides stated as certified finite
mixed-word checklists.

The lower checklist supplies the same-error mixed frontier; the upper checklist
supplies the broad upper mixed remainder.  Thus both local spike inputs are now
finite word-by-word certification problems. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedChecklist_lowerMixedChecklist_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalanAtRatio :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio R)
    (hLowerMixedChecklist :
      LowerConcreteCertifiedMixedWordChecklist R eps 3)
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hUpperMeanDeficit :
      upperConcreteModelMeanThreeCatalanScaledDeficitTendsToTop R)
    (hUpperExp :
      ∃ cUpper : ℝ,
        UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperMixedChecklist :
      UpperConcreteCertifiedMixedWordChecklist R eps 3) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_directHeightBands_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceTail_upperExponentialConcentrationExists_upperMeanScaledDeficit_upperMixedChecklist_lowerMixedChecklist_k3
    R hε
    (finRealSphereAutoHeightBandsDirectGainSup_of_averageGainSup
      hLemma43AutoHeightBands)
    hThreeCatalanAtRatio hLowerMixedChecklist hVariance hUpperMeanDeficit
    hUpperExp hUpperMixedChecklist

/-- The cleaned branch-split upper mixed input cannot be closed by the
canonical actual-model scalar envelopes at length three.

The new endpoint exposes `UpperConcreteMixedDefectCaseLimits`.  If one plugs in
the canonical actual-model choices for `Abound`, `L2bound`, `L1bound`,
`Q2bound`, and `Q1bound`, the one-quadratic branch alone contradicts the
checked no-go theorem.  Thus the remaining upper mixed input is not merely a
missing wrapper: the canonical scalar envelope must be replaced or sharpened. -/
theorem
    upper_concrete_cleaned_defectCase_endpoint_canonical_upperMixed_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperDefectLimits :
      UpperConcreteMixedDefectCaseLimits 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordL1bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)
        (upperConcreteModelMixedWordQ1bound R eps 3)) :
    False :=
  upperConcreteModel_oneQuadraticMixedTermLimit_not_canonical
    (R := R) hε hUpperDefectLimits.2.1

/-- The fixed-slack local-expansion route cannot supply the cleaned endpoint's
upper exponential concentration input at length three.

This does not refute
`∃ c, UpperConcreteModelMomentExponentialDeviationSetBound R c 3`.  It refutes
the tempting proof path that keeps a half-mass background set while asking for
the scalar local-expansion budget
`aSlack^3 + etaSlack + τ < upperCanonicalTau`, where
`upperCanonicalTau slack d = slack / d`.  Since `etaSlack` is fixed positive
for fixed slack and `slack / d -> 0`, that package is inconsistent. -/
theorem
    upper_concrete_cleaned_exponential_localExpansion_halfMassBudget_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  3 d)
                3))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ 3 + etaSlack slack + τ slack d <
            upperCanonicalTau slack d) :
    False :=
  upperConcreteModel_localExpansionCanonicalTauBudget_halfMass_impossible
    (R := R) (k := 3) (aSlack := aSlack) (etaSlack := etaSlack)
    (M := M) (τ := τ) ha hEta hK_half hBudget

/-- Ratio-parametric Catalan variance-stack endpoint with the lower
partial-transpose mixed-word inputs reduced to scalar scale comparisons.

This wrapper removes the theorem-facing direct word estimates for the lower
one-column local spike.  The remaining lower mixed obligations are the scalar
comparisons between the concrete background threshold and the fixed PT envelope
parameter. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTScaleComparisonCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_fromRatio
        R.sample)
    (M : ℝ)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0))
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanFromRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M
    (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
      R (by norm_num : 3 ≤ 3) hε hOneScale)
    (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
      R (by norm_num : 3 ≤ 3) hε hManyScale)
    hVariance hMeanCompare hUpperExp hUpperWord hUpperTerm

/-- The ratio-parametric scale-comparison lower-PT wrapper above is diagnostic
at length three.

Its lower mixed inputs use the fixed budget `max M 0`.  That budget is
nonnegative, and the checked lower-side obstruction rules out the paired
one-`Q` and many-`Q` scale comparisons for every nonnegative fixed budget. -/
theorem
    upper_concrete_ratioCatalan_scaleComparison_endpoint_lowerPTScaleComparisons_input_impossible_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (M : ℝ)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0))
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps (max M 0)) :
    False :=
  lowerConcretePTMixedWordScaleComparisons_three_not_uniform
    (R := R) (ε := eps) hε (max M 0) (le_max_right M 0)
    ⟨hOneScale, hManyScale⟩

/-- Named-input live endpoint with the broad upper mixed remainder split into a
deterministic model-level mixed-word bound and scalar envelope limits.

This is a proof-frontier sharpening of the mixed-remainder route.  It does not
use the refuted canonical scalar branch package; the caller may choose any
envelopes that make both the word bound and term limit true. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hLowerExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hLowerExpTail
    hMeanCompare hUpperExp
    (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
      R (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Named-input live endpoint with the canonical actual-model mixed-word bounds
wired in.

The three branchwise word estimates are supplied by the checked canonical
actual-model local matrix bounds.  The remaining upper mixed input is now only
the scalar envelope-limit package for those canonical envelopes. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_canonicalWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hLowerExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordL1bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)
        (upperConcreteModelMixedWordQ1bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hLowerExpTail
    hMeanCompare hUpperExp
    (UpperConcreteModelMixedWordBound_of_caseBounds
      R
      (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
        R (by norm_num : 3 ≤ 3) hε)
      (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
        R (by norm_num : 3 ≤ 3) hε)
      (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
        R (by norm_num : 3 ≤ 3) hε))
    hUpperTerm

/-- The live canonical-word wrapper above is diagnostic at length three.

It wires in the checked canonical actual-model word estimates, but the remaining
bundled canonical scalar term limit is inconsistent.  Thus this endpoint cannot
be closed by proving the naive canonical scalar packet; the live route must use
different envelopes or prove the broad mixed-remainder input directly. -/
theorem
    upper_concrete_live_canonicalWordBound_termLimit_endpoint_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordL1bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)
        (upperConcreteModelMixedWordQ1bound R eps 3)) :
    False := by
  apply upperConcreteModel_multiDefectMixedTermLimit_not_canonical
    (R := R) hε
  intro slack hslack w hMixed hNotOneLinear hNotOneQuadratic
  simpa [UpperConcreteModelMixedTermLimit, localExpansionMixedWordEnvelopeTerm,
    hNotOneLinear, hNotOneQuadratic] using
    hUpperTerm slack hslack w hMixed

/-- Average-form direct-PT-scalar endpoint with the broad upper mixed remainder
split into its deterministic word-bound input and scalar envelope limit. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_mixedRemainder_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hVariance
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hUpperExp
    (UpperConcreteModelMixedRemainderBound_of_modelMixedWordBound_and_termLimit
      R (by norm_num : 1 ≤ 3) hUpperWord hUpperTerm)

/-- Named-geometry version of the average-form direct-PT-scalar endpoint with
the broad upper mixed remainder split into word bounds and scalar envelope
limits.

This removes the raw auto-height-band formula from the theorem-facing
interface; the geometry input is the named packet used by the other live
endpoints. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperWord :
      UpperConcreteModelMixedWordBound R eps 3
        Abound L2bound L1bound Q2bound Q1bound)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        Abound L2bound L1bound Q2bound Q1bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    R hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hThreeCatalan M hOne hMany hVariance
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hUpperExp
    hUpperWord hUpperTerm

/-- Average-form direct-PT-scalar endpoint with the upper mixed input split all
the way to the casewise word estimates and casewise scalar limits. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_caseMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_modelMixedWordBound_termLimit_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOne hMany hVariance
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hUpperExp
    (UpperConcreteModelMixedWordBound_of_caseBounds
      R hUpperOneLinearWord hUpperOneQuadraticWord hUpperMultiWord)
    (UpperConcreteModelMixedTermLimit_of_caseLimits
      hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm)

/-- Named-geometry version of the casewise upper mixed endpoint.

This keeps the theorem-facing geometry input at the same named level as the
neighboring endpoints; the raw auto-height-band formula is only unfolded inside
this adapter. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_caseMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearWord :
      UpperConcreteModelOneLinearMixedWordBound R eps 3 Abound L1bound)
    (hUpperOneQuadraticWord :
      UpperConcreteModelOneQuadraticMixedWordBound R eps 3 Abound Q1bound)
    (hUpperMultiWord :
      UpperConcreteModelMultiDefectMixedWordBound R eps 3 Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_caseMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    R hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hThreeCatalan M hOne hMany hVariance
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hUpperExp
    hUpperOneLinearWord hUpperOneQuadraticWord hUpperMultiWord
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-form direct-PT-scalar endpoint with the canonical actual-model word
estimates wired in.

Compared with the six-leaf casewise endpoint above, this wrapper supplies the
three word-bound leaves from the canonical actual-model word envelopes.  The
three scalar limits remain explicit; for the canonical envelopes these scalar
limits are the live obstruction. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_canonicalWordBounds_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_caseMixedWordBounds_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    R hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hThreeCatalan M hOne hMany hVariance
    (upperLowerConcreteMeanCompare.raw hMeanCompare) hUpperExp
    (UpperConcreteModelOneLinearMixedWordBound_of_canonical_model
      R (by norm_num : 3 ≤ 3) hε)
    (UpperConcreteModelOneQuadraticMixedWordBound_of_canonical_model
      R (by norm_num : 3 ≤ 3) hε)
    (UpperConcreteModelMultiDefectMixedWordBound_of_canonical_model
      R (by norm_num : 3 ≤ 3) hε)
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- The balanced average canonical-word/direct-PT endpoint has an inconsistent
canonical upper scalar packet at length three.

Even before discussing the lower direct PT scalar inputs, the canonical
upper one-linear scalar limit already contradicts the actual-model growth.
Thus this endpoint is diagnostic unless the upper scalar envelopes are changed
away from the naive canonical packet. -/
theorem
    upper_concrete_balancedAverage_canonicalWordBounds_directPT_endpoint_caseTerm_packet_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    False := by
  let _ := hUpperOneQuadraticTerm
  let _ := hUpperMultiTerm
  exact
    upperConcreteModel_oneLinearMixedTermLimit_not_canonical
      (R := R) hε hUpperOneLinearTerm

/-- Average-form canonical-word endpoint with the lower PT mixed inputs reduced
to their scalar scale-comparison leaves.

Compared with the direct-PT-scalar endpoint above, this wrapper supplies the two
direct scalar trace bounds from the local trace estimates plus the exact
one-`Q` and many-`Q` scale comparisons.  This is still conditional: the scalar
comparisons remain theorem-facing inputs. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_canonicalWordBounds_caseTermLimits_lowerPTScaleComparisons_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0))
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_canonicalWordBounds_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M
    (lowerConcretePTMixedWordOneQDirectScalarBound_of_scaleComparison
      R (by norm_num : 3 ≤ 3) hε hOneScale)
    (lowerConcretePTMixedWordManyQDirectScalarBound_of_scaleComparison
      R (by norm_num : 3 ≤ 3) hε hManyScale)
    hVariance hMeanCompare hUpperExp
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Average-form canonical-word endpoint with the lower background variance
stack supplied by the stronger deleted-background exponential tail source.

Compared with the scale-comparison endpoint above, this wrapper replaces the
paper-facing `C / d^4` variance/Chebyshev packet by the exponential deviation
tail input that already implies it. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_exponentialDeletedBackgroundTail_upperExponentialConcentration_meanCompare_canonicalWordBounds_caseTermLimits_lowerPTScaleComparisons_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0))
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps (max M 0))
    (hLowerExpTail :
      lowerConcreteDeletedBackgroundMomentExponentialDeviationTailBound R 3)
    (hMeanCompare : upperLowerConcreteMeanCompare R 3)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3))
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3))
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_canonicalWordBounds_caseTermLimits_lowerPTScaleComparisons_normalizedM_k3
    R hε hLemma43AutoHeightBands hThreeCatalan M hOneScale hManyScale
    (deletedColumnSphericalMoment_variance_le_const_div_d4_of_exponentialDeviationTailBound
      R 3 hLowerExpTail)
    hMeanCompare hUpperExp
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- The current normalized lower-PT scale-comparison branch is inconsistent at
length three.

The endpoint above exposes `lowerConcretePTMixedWordOneQScaleComparison R 3 eps
(max M 0)`.  Since `max M 0` is nonnegative, the checked lower-side no-go theorem
rules out exactly that input.  Thus this branch is a diagnostic/vacuous route,
not a remaining theorem to prove from mathlib. -/
theorem
    upper_concrete_canonical_scaleComparison_endpoint_lowerPTOneQ_input_impossible_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (M : ℝ)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0)) :
    False :=
  lowerConcretePTMixedWordOneQScaleComparison_three_not_uniform
    (R := R) (ε := eps) hε (max M 0) (le_max_right M 0) hOneScale

/-- The current normalized lower-PT scale-comparison packet is inconsistent at
length three.

The newest sharp ratio-Catalan variance-stack endpoint exposes the pair
`lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0)` and
`lowerConcretePTMixedWordManyQScaleComparison R 3 eps (max M 0)`.  The fixed
`max M 0` budget is incompatible with the checked growth of the concrete
deleted-background threshold, so this paired scale-comparison branch is not a
proof path. -/
theorem
    upper_concrete_varianceStack_scaleComparison_endpoint_lowerPTScaleComparisons_input_impossible_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (M : ℝ)
    (hOneScale :
      lowerConcretePTMixedWordOneQScaleComparison R 3 eps (max M 0))
    (hManyScale :
      lowerConcretePTMixedWordManyQScaleComparison R 3 eps (max M 0)) :
    False :=
  lowerConcretePTMixedWordScaleComparisons_three_not_uniform
    (R := R) (ε := eps) hε (max M 0) (le_max_right M 0)
    ⟨hOneScale, hManyScale⟩

/-- The current canonical upper one-linear scalar-limit input is inconsistent at
length three.

The endpoint above exposes the actual-model canonical one-linear scalar limit.
The checked upper-side no-go theorem rules out that exact limit, so this
canonical scalar-limit branch is diagnostic/vacuous as stated. -/
theorem
    upper_concrete_canonical_caseTerm_endpoint_oneLinear_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL1bound R eps 3)) :
    False :=
  upperConcreteModel_oneLinearMixedTermLimit_not_canonical
    (R := R) hε hUpperOneLinearTerm

/-- The current canonical upper one-quadratic scalar-limit input is inconsistent
at length three.

The endpoint above exposes the actual-model canonical one-quadratic scalar
limit.  The checked upper-side no-go theorem rules out that exact limit. -/
theorem
    upper_concrete_canonical_caseTerm_endpoint_oneQuadratic_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordQ1bound R eps 3)) :
    False :=
  upperConcreteModel_oneQuadraticMixedTermLimit_not_canonical
    (R := R) hε hUpperOneQuadraticTerm

/-- The current canonical upper multi-defect scalar-limit input is inconsistent
at length three.

The endpoint above exposes the actual-model canonical multi-defect scalar
limit.  The checked upper-side no-go theorem rules out that exact limit. -/
theorem
    upper_concrete_canonical_caseTerm_endpoint_multiDefect_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)) :
    False :=
  upperConcreteModel_multiDefectMixedTermLimit_not_canonical
    (R := R) hε hUpperMultiTerm

/-- The bundled canonical upper mixed scalar-limit input is inconsistent at
length three.

The bundled predicate includes every mixed word.  Specializing it to the
multi-defect branch gives the already refuted canonical multi-defect scalar
limit. -/
theorem
    upper_concrete_canonical_mixedTerm_endpoint_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hUpperTerm :
      UpperConcreteModelMixedTermLimit 3
        (upperConcreteModelMixedWordAbound R)
        (upperConcreteModelMixedWordL2bound R eps 3)
        (upperConcreteModelMixedWordL1bound R eps 3)
        (upperConcreteModelMixedWordQ2bound R eps 3)
        (upperConcreteModelMixedWordQ1bound R eps 3)) :
    False := by
  apply upperConcreteModel_multiDefectMixedTermLimit_not_canonical
    (R := R) hε
  intro slack hslack w hMixed hNotOneLinear hNotOneQuadratic
  simpa [UpperConcreteModelMixedTermLimit, localExpansionMixedWordEnvelopeTerm,
    hNotOneLinear, hNotOneQuadratic] using
    hUpperTerm slack hslack w hMixed

/-- The fixed-slack local-expansion route to the upper exponential
concentration input is inconsistent at length three.

This does not refute the concentration input itself.  It refutes the tempting
canonical budget package that tries to prove it while keeping a half-mass
typical set and a positive fixed error allowance under
`upperCanonicalTau slack d`, which tends to zero. -/
theorem
    upper_concrete_exponential_localExpansion_halfMassBudget_input_impossible_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {aSlack etaSlack : ℝ → ℝ}
    {M τ : ℝ → ℕ → ℝ}
    (ha : ∀ slack : ℝ, 0 < slack → 0 ≤ aSlack slack)
    (hEta : ∀ slack : ℝ, 0 < slack → 0 < etaSlack slack)
    (hK_half :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          1 / 2 ≤
            (PptFactorization.AppendixB.sphericalModelMeasure
              (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
              (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
              (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                (R.sample d))).real
              (backgroundTypicalSet
                (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                  (R.sample d))
                (upperConcreteN d) (M slack d) (τ slack d)
                (upperConcreteMean
                  (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
                  (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
                  (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
                    (R.sample d))
                  3 d)
                3))
    (hBudget :
      ∀ slack : ℝ, 0 < slack →
        ∀ᶠ d in atTop,
          aSlack slack ^ 3 + etaSlack slack + τ slack d <
            upperCanonicalTau slack d) :
    False :=
  upperConcreteModel_localExpansionCanonicalTauBudget_halfMass_impossible
    (R := R) (k := 3) (aSlack := aSlack) (etaSlack := etaSlack)
    (M := M) (τ := τ) ha hEta hK_half hBudget

/-- Average-form version of the current direct-PT-scalar mixed endpoint.

This exposes the lower mixed input as the two concrete PT scalar trace estimates
rather than the bundled `lowerConcreteMixedErrorFrontier`. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 < r → r < Real.pi →
          ∀ ⦃η : ℝ⦄, 0 < η →
            ∃ epsBand tauSep : ℝ,
              0 < epsBand ∧
                0 < tauSep ∧
                  ∀ ⦃A : Set (PptFactorization.AppendixB.FinRealSphere n)⦄,
                    PptFactorization.AppendixB.FinRealSphereHalfMassCompetitor n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) A →
                    PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r
                          (PptFactorization.AppendixB.finRealSphereClosedHemisphere n
                            (PptFactorization.AppendixB.finRealSphereNorthPole n :
                              PptFactorization.AppendixB.FinRealEuclideanSpace n)) + η ≤
                      PptFactorization.AppendixB.finRealSphereNeighbourhoodComplementMass n
                        (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n) r A →
                    ∃ Cmodel pole a tauMax,
                      0 < tauMax ∧
                        MeasurableSet Cmodel ∧
                          (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              Cmodel =
                            (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                              A ∧
                            epsBand ≤
                              (PptFactorization.AppendixB.finRealSurfaceProbabilityMeasure n).real
                                (symmDiff Cmodel A) ∧
                              ∀ ⦃tauBand : ℝ⦄,
                                0 < tauBand → tauBand ≤ tauMax →
                                  ∃ avg : ℝ,
                                    SphericalPolarization.GeometricKernel.HasRectangularBlockLowerBound
                                      n tauSep
                                      (PptFactorization.AppendixB.finRealPolarizationMuMinus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandBelow
                                          n pole a tauBand))
                                      (PptFactorization.AppendixB.finRealPolarizationMuPlus
                                        Cmodel A
                                        (PptFactorization.AppendixB.finRealSphereHeightBandAbove
                                          n pole a tauBand))
                                      avg ∧
                                    avg ≤
                                      sSup
                                        (PptFactorization.AppendixB.finRealSpherePolarizationObjectiveGainValues
                                          n r A))
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsDirectGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    R hε
    (lemma43AutoHeightBandsDirectGainSup_of_averageGainSup hLemma43AutoHeightBands)
    hThreeCatalan M hOne hMany hVariance hMeanCompare hUpperExp
    hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

/-- Named-geometry version of the direct-PT-scalar branch-envelope endpoint.

This removes the raw auto-height-band formula from the theorem-facing
interface.  The remaining visible inputs are the balanced Catalan estimate,
the two lower PT direct scalar estimates, variance, mean comparison, upper
concentration, and the branch envelope/limit packet. -/
theorem
    upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSupNamed_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    (R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    {eps : ℝ} (hε : 0 < eps)
    (hLemma43AutoHeightBands : finRealSphereAutoHeightBandsAverageGainSup)
    (hThreeCatalan :
      lowerDeletedColumnBackgroundMomentThreeCatalanDOverDBound_atBalancedRatio
        R)
    (M : ℝ)
    (hOne :
      lowerConcretePTMixedWordOneQDirectScalarBound R 3 eps (max M 0))
    (hMany :
      lowerConcretePTMixedWordManyQDirectScalarBound R 3 eps (max M 0))
    (hVariance :
      deletedColumnSphericalMoment_variance_le_const_div_d4 R 3)
    (hMeanCompare :
      ∀ᶠ d in atTop,
        upperConcreteMean
            (p := PptFactorization.AppendixB.ConcreteModel.LeftIndex d)
            (q := PptFactorization.AppendixB.ConcreteModel.RightIndex d)
            (σ := PptFactorization.AppendixB.ConcreteModel.SampleIndex
              (R.sample d))
            3 d ≤
          lowerConcreteDeletedBackgroundMean R 3 d)
    {cUpper : ℝ}
    (hUpperExp :
      UpperConcreteModelMomentExponentialDeviationSetBound R cUpper 3)
    {Abound L2bound L1bound Q2bound Q1bound : ℝ → ℕ → ℝ}
    (hUpperOneLinearDom :
      UpperConcreteModelOneLinearMixedWordEnvelopeDomination R eps 3
        Abound L1bound)
    (hUpperOneQuadraticDom :
      UpperConcreteModelOneQuadraticMixedWordEnvelopeDomination R eps 3
        Abound Q1bound)
    (hUpperMultiDom :
      UpperConcreteModelMultiDefectMixedWordEnvelopeDomination R eps 3
        Abound L2bound Q2bound)
    (hUpperOneLinearTerm :
      UpperConcreteOneLinearMixedTermLimit 3 Abound L1bound)
    (hUpperOneQuadraticTerm :
      UpperConcreteOneQuadraticMixedTermLimit 3 Abound Q1bound)
    (hUpperMultiTerm :
      UpperConcreteMultiDefectMixedTermLimit 3 Abound L2bound Q2bound) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ d in atTop,
        Real.log (upperConcreteModelTargetProb R eps 3 d) / spikeSpeed 3 d ≤
          -spikeRate 3 R.lam eps + η :=
  upper_eventual_from_concrete_model_of_lemma43AutoHeightBandsAverageGainSup_capConeFlatteningMap_lowerCanonicalColumnPipeline_threeCatalanAtBalancedRatio_varianceStack_upperExponentialConcentration_meanCompare_branchEnvelopeDominations_caseTermLimits_lowerPTDirectScalarCases_normalizedM_k3
    R hε (finRealSphereAutoHeightBandsAverageGainSup.raw hLemma43AutoHeightBands)
    hThreeCatalan M hOne hMany hVariance hMeanCompare hUpperExp
    hUpperOneLinearDom hUpperOneQuadraticDom hUpperMultiDom
    hUpperOneLinearTerm hUpperOneQuadraticTerm hUpperMultiTerm

end AppendixB
