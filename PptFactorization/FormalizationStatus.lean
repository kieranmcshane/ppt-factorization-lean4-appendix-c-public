import PptFactorization.AppendixCMainResult
import PptFactorization.AppendixBFinal
import PptFactorization.ComplexGaussianWick
import PptFactorization.Verify

/-!
# Public formalization status index

This file is a shallow, machine-checkable map of the public theorem surface.
It imports the relevant endpoints and re-exports them under namespaces that
encode their claim status.  It intentionally proves no new mathematical facts.
-/

namespace PptFactorization
namespace FormalizationStatus

namespace AppendixC

/- Conditional algebraic spine: these endpoints consume explicit supplier
hypotheses such as trace identities, rootwise rank-one data, kernel equations,
divisibility, coprimality, and the coefficient equation. -/
namespace AlgebraicSpine
export AppendixCMainResult
  (appendixC_algebraic_spine_universality
   appendixC_main_algebraic_universality
   appendixC_congruence_mod_threshold_polynomial
   appendixC_rootwise_coefficient_eq_neg_one)
end AlgebraicSpine

/- Canonical engineered all-`m` branch.  This is not the physical determinant
branch for all `m`. -/
namespace CanonicalAllM
export AppendixCMainResult
  (appendixC_canonical_universal_scaling_law
   appendixC_self_contained_tridiagonal_scaling_law
   appendixC_self_contained_tridiagonal_sharpness)
end CanonicalAllM

/- Concrete physical determinant cases currently checked in this snapshot. -/
namespace PhysicalSmallCases
export AppendixCMainResult
  (appendixC_physical_scaling_law_m1
   appendixC_physical_scaling_law_m2
   appendixC_physical_scaling_law_m3)
end PhysicalSmallCases

end AppendixC

namespace AppendixB

/- Appendix B assembly endpoints that still expose analytic hypotheses in
their theorem statements. -/
namespace ConditionalAssembly
export PptFactorization.AppendixB
  (final_appendixB_assembly_no_structure_inputs)
end ConditionalAssembly

end AppendixB

namespace GaussianWick

/- No-input concrete Gaussian matrix-entry Wick/Isserlis endpoint. -/
namespace NoInput
export PptFactorization.ComplexGaussianWick
  (concrete_wick_isserlis_entry_monomial
   concrete_wick_isserlis_entry_monomial_noInput)
end NoInput

end GaussianWick

namespace FiniteDeterminants

/- Small determinant factorization cases certified as Lean theorems. -/
namespace TheoremCertifiedSmallCases
export PPT
  (factorization_m0
   factorization_m1
   factorization_m2)
end TheoremCertifiedSmallCases

end FiniteDeterminants

end FormalizationStatus
end PptFactorization
