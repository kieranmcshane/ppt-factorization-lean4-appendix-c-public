import PptFactorization.AppendixBLowerBoundClosure

/-!
# Beta `propext` bisect audit

Run with:

```bash
lake env lean tools/AuditBetaPropextBisect.lean
```

The order below follows the local dependency chain feeding
`betaMeasure_nat_real_Icc_lower`.
-/

/- Suspect mathlib dependencies inside `betaMeasure_nat_real_Icc_lower`. -/
#print axioms MeasureTheory.withDensity_apply
#print axioms MeasureTheory.lintegral_mono_ae
#print axioms MeasureTheory.ae_restrict_of_forall_mem
#print axioms Real.volume_Icc
#print axioms ENNReal.ofReal_le_iff_le_toReal

/- External dependency used by `beta_nat_eq_factorial_ratio`. -/
#print axioms Real.Gamma_nat_eq_factorial

/- Local arithmetic and pointwise-density chain. -/
#print axioms AppendixB.beta_nat_eq_factorial_ratio
#print axioms AppendixB.beta_nat_le_one
#print axioms AppendixB.one_le_one_div_beta_nat
#print axioms AppendixB.betaPDFReal_nat_lower_on_Icc

/- Local integral-measure endpoint. -/
#print axioms AppendixB.betaMeasure_nat_real_Icc_lower

/- Propagation through the Beta package and canonical constructors. -/
#print axioms AppendixB.betaColumnMeasureIntervalLowerBound_betaColumnMeasure
#print axioms AppendixB.integerBetaColumnMeasure_betaColumnMeasure
#print axioms AppendixB.canonicalIntegerBetaColumnMeasure
#print axioms AppendixB.CanonicalColumnMassBetaLaw.of_R_hasCanonicalBetaLaw
#print axioms AppendixB.CanonicalColumnMassBetaLaw.betaColumnIntervalLowerBound
#print axioms AppendixB.CanonicalSphericalOneColumnDecompositionIndependence.canonicalColumnMassBetaLaw_noInput
#print axioms AppendixB.CanonicalSphericalOneColumnDecompositionIndependence.betaColumnIntervalLowerBound

/- Propagation into the lower closure and scalar-limits constructor. -/
#print axioms AppendixB.lower_betaIntervalLowerBound_canonicalProbability_pointwise
#print axioms AppendixB.lower_concrete_hBeta
#print axioms AppendixB.SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits
