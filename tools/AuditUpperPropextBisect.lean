import PptFactorization.AppendixBLowerBoundClosure
import PptFactorization.AppendixBUpperBoundClosure

/-!
# Upper `propext` residue audit

Run with:

```bash
lake env lean tools/AuditUpperPropextBisect.lean
```

This separates the shared lower/upper spine from the upper-specific
local-expansion path.  At the moment the shared spine still carries `propext`,
so this harness does not claim an upper-only residue; it records whether the
upper stack also carries the same foundational dependency.
-/

/- Shared spine status. -/
#print axioms AppendixB.betaMeasure_nat_real_Icc_lower
#print axioms AppendixB.CanonicalSphericalOneColumnDeletedBackgroundDecompositionIndependence.sphericalLaw
#print axioms AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel

/- Abstract upper input and sharp-spherical upper spine. -/
#print axioms AppendixB.AbstractSpikeUpperBoundInput.eventual_log_over_speed_upper
#print axioms AppendixB.abstractSpikeUpperBoundInput_of_sharp_spherical_isoperimetry_slack_radius
#print axioms AppendixB.SpikeUpperBoundInput.of_sharp_spherical_isoperimetry_slack_radius
#print axioms AppendixB.eventual_log_over_spikeSpeed_upper_of_sharp_spherical_isoperimetry_slack_radius
#print axioms AppendixB.SpikeUpperBoundInput.eventual_log_over_spikeSpeed_upper

/- Upper-specific local-expansion path feeding the clean closure endpoint. -/
#print axioms AppendixB.eventual_localExpansion_budget_of_tau_tendsto
#print axioms AppendixB.eventual_upperAspect_of_tendsto_ratio
#print axioms AppendixB.eventual_upperRemainder_of_tendsto_zero
#print axioms AppendixB.backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
#print axioms AppendixB.eventual_backgroundMomentDeviation_probability_le_sharpIso_of_localExpansion
#print axioms AppendixB.eventual_targetProbability_le_sharp_spherical_tail_of_localExpansion
#print axioms AppendixB.eventual_log_over_spikeSpeed_upper_of_localExpansion_scalar_limits

/- Public upper closure endpoints. -/
#print axioms AppendixB.upper_eventual_from_localExpansion_scalarLimits
#print axioms AppendixB.upper_eventual_from_input
