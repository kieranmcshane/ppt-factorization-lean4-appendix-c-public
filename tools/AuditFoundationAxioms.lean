import PptFactorization.AppendixBLowerBoundClosure
import PptFactorization.AppendixBUpperBoundClosure

/-!
# Minimal foundation-axiom audit harness

Run with:

```bash
lake env lean tools/AuditFoundationAxioms.lean
```

This file intentionally audits only the small set of lower/upper endpoint
theorems and spine lemmas currently used to track the remaining foundational
axiom dependency, especially `propext`.
-/

#print axioms AppendixB.betaMeasure_nat_real_Icc_lower
#print axioms AppendixB.betaColumnMeasureIntervalLowerBound_betaColumnMeasure
#print axioms AppendixB.CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
#print axioms AppendixB.columnProb_le_upperTailProb_of_closed_deterministic_blocks
#print axioms AppendixB.SpikeLowerBoundInput.of_oneColumn_probability_pipeline_scalar_limits

#print axioms AppendixB.lower_spikeInput_concreteScalars_of_concreteBeta
#print axioms AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel
#print axioms AppendixB.upper_eventual_from_localExpansion_scalarLimits
#print axioms AppendixB.upper_eventual_from_input
