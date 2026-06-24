import PptFactorization.AppendixCUniversality
import PptFactorization.HankelBridge
import PptFactorization.PhysicalScalingLaw
import PptFactorization.UniversalScalingLaw
import PptFactorization.UniversalScalingLawProof

/-!
# Appendix C reductions and scaling endpoints, consolidated

This file is a standalone consolidation of the Lean material behind Appendix C.
It intentionally does not reprove every imported lemma inline.  Instead, it
collects the already-checked routes into one file whose public endpoints state
the mathematically relevant forms of the result.

There are three layers.

* `appendixC_rootwise_coefficient_eq_neg_one` is the exact algebraic Appendix C
  endpoint: once the trace identity, balanced determinant divisibility, root
  list, rank-one trace formula, Hankel-kernel equations, coprimality, and the
  first-order coefficient equation are supplied, the selected coefficient is
  `-1`.

* `appendixC_main_algebraic_universality` is the same endpoint in its most
  useful paper-facing form: it returns both the determinant congruence
  `g ∣ f₁ - f₀'` and the coefficient identity `coeff = -1`.

* `appendixC_canonical_universal_scaling_law` is the no-input
  tridiagonal/Chebyshev endpoint: for every `m > 0` there is a smooth local
  threshold branch with first derivative `-1`, hence the physical-scale
  estimate with correction `-1/d₁`.  This is the route through the
  canonical engineered ambient function, not a proof that the actual physical
  finite-`d₁` determinant follows this branch for all `m`.

The concrete physical determinant is recovered in the already-proved small
  cases `m = 1,2,3`, exposed below as separate endpoints.  For all `m`, the
algebraic endpoint above states exactly what has to be checked to identify a
given physical finite-`d₁` determinant with the universal Appendix C spine.
-/

open Polynomial
open scoped BigOperators

namespace AppendixCMainResult

section AlgebraicAppendixC

variable {K : Type*} [Field K]

/--
The exact rootwise coefficient endpoint of Appendix C.

Mathematically, this is the following statement.  Let `g` be the polynomial whose
roots are the balanced threshold roots under consideration.  Suppose:

* `TraceIdentity m f₀ f₁ Sigma` is the determinant-level trace identity
  `X (f₁ - f₀') = (m+1) f₀ - Sigma`;
* `g ∣ f₀`, so the selected roots are balanced determinant roots;
* `g` is the product of the listed linear factors;
* at each listed root, `Sigma` is a rank-one convolution trace and the same
  vector satisfies the Hankel-kernel equations;
* `g` is coprime to `X`;
* `α` is a root of `g` and `f₀'(α) ≠ 0`;
* the selected local root has first-order coefficient equation
  `coeff * f₀'(α) + f₁(α) = 0`.

Then the first-order coefficient is exactly `-1`.
-/
theorem appendixC_rootwise_coefficient_eq_neg_one
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α coeff : K)
    (q : K → K) (c v : K → ℕ → K)
    (hcoeff : coeff * eval α (derivative f₀) + eval α f₁ = 0)
    (htrace : AppendixCUniversality.TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma : ∀ a, a ∈ roots →
      eval a Sigma =
        q a * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          v a i * v a j *
            (∑ b ∈ Finset.range (i + j + 2),
              c a b * c a (i + j + 1 - b))))
    (hkernel : ∀ a, a ∈ roots → ∀ i, i ≤ m →
      (∑ j ∈ Finset.range (m + 1), v a j * c a (i + j + 1)) = 0)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    coeff = -1 :=
  AppendixCUniversality.selected_first_order_coefficient_eq_neg_one_of_rootwise_rankOne_trace_data
    m roots g f₀ f₁ Sigma α coeff q c v hcoeff htrace hg_f₀ hg_prod
    hSigma hkernel hcop hroot hf₀'

/--
The congruence form of Appendix C: under the trace identity and rootwise
vanishing package, `f₁` and `f₀'` agree modulo the balanced threshold factor
`g`.
-/
theorem appendixC_congruence_mod_threshold_polynomial
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X])
    (htrace : AppendixCUniversality.TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma_roots : ∀ a, a ∈ roots → eval a Sigma = 0)
    (hcop : IsCoprime g X) :
    g ∣ f₁ - derivative f₀ :=
  AppendixCUniversality.universality_congruence_of_trace_identity_rootwise
    m roots g f₀ f₁ Sigma htrace hg_f₀ hg_prod hSigma_roots hcop

/--
The paper-facing algebraic reduction at the heart of Appendix C.

It packages the two actual conclusions of the algebraic proof:

* the determinant-level congruence `f₁ ≡ f₀'` modulo the balanced threshold
  factor `g`;
* the selected first-order threshold coefficient is `-1`.

This theorem is conditional on the rootwise data that the paper must produce:
trace identity, balanced-root divisibility, explicit root factor, rank-one
convolution trace formula, Hankel-kernel equations, coprimality with `X`, and
the linearized root equation.  It is not a no-input all-`m` physical determinant
theorem.
-/
theorem appendixC_main_algebraic_universality
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α coeff : K)
    (q : K → K) (c v : K → ℕ → K)
    (hcoeff : coeff * eval α (derivative f₀) + eval α f₁ = 0)
    (htrace : AppendixCUniversality.TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma : ∀ a, a ∈ roots →
      eval a Sigma =
        q a * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          v a i * v a j *
            (∑ b ∈ Finset.range (i + j + 2),
              c a b * c a (i + j + 1 - b))))
    (hkernel : ∀ a, a ∈ roots → ∀ i, i ≤ m →
      (∑ j ∈ Finset.range (m + 1), v a j * c a (i + j + 1)) = 0)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    (g ∣ f₁ - derivative f₀) ∧ coeff = -1 := by
  have hSigma_roots : ∀ a, a ∈ roots → eval a Sigma = 0 := by
    intro a ha
    exact AppendixCUniversality.sigmaRoot_eq_zero_of_rankOne_trace_formula_range
      m (c a) (v a) (q a) (eval a Sigma) (hSigma a ha) (hkernel a ha)
  constructor
  · exact appendixC_congruence_mod_threshold_polynomial
      m roots g f₀ f₁ Sigma htrace hg_f₀ hg_prod hSigma_roots hcop
  · exact appendixC_rootwise_coefficient_eq_neg_one
      m roots g f₀ f₁ Sigma α coeff q c v hcoeff htrace hg_f₀ hg_prod
      hSigma hkernel hcop hroot hf₀'

/--
Accurately named alias for `appendixC_main_algebraic_universality`.

This endpoint is an algebraic spine theorem: it consumes explicit supplier
hypotheses and returns the determinant congruence plus coefficient `-1`.  It is
not a no-input physical all-`m` determinant theorem.
-/
theorem appendixC_algebraic_spine_universality
    (m : ℕ) (roots : Finset K) (g f₀ f₁ Sigma : K[X]) (α coeff : K)
    (q : K → K) (c v : K → ℕ → K)
    (hcoeff : coeff * eval α (derivative f₀) + eval α f₁ = 0)
    (htrace : AppendixCUniversality.TraceIdentity m f₀ f₁ Sigma)
    (hg_f₀ : g ∣ f₀)
    (hg_prod : g = ∏ a ∈ roots, (X - C a : K[X]))
    (hSigma : ∀ a, a ∈ roots →
      eval a Sigma =
        q a * (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          v a i * v a j *
            (∑ b ∈ Finset.range (i + j + 2),
              c a b * c a (i + j + 1 - b))))
    (hkernel : ∀ a, a ∈ roots → ∀ i, i ≤ m →
      (∑ j ∈ Finset.range (m + 1), v a j * c a (i + j + 1)) = 0)
    (hcop : IsCoprime g X)
    (hroot : eval α g = 0)
    (hf₀' : eval α (derivative f₀) ≠ 0) :
    (g ∣ f₁ - derivative f₀) ∧ coeff = -1 :=
  appendixC_main_algebraic_universality
    m roots g f₀ f₁ Sigma α coeff q c v hcoeff htrace hg_f₀ hg_prod
    hSigma hkernel hcop hroot hf₀'

end AlgebraicAppendixC

section ChebyshevTridiagonalSpine

/--
The tridiagonal/Chebyshev spine at the balanced threshold:
`d_{m+1}(α_m)=0`, the neighbouring minor is positive, and the
Christoffel--Darboux normalization is available.
-/
theorem appendixC_chebyshev_tridiagonal_spine (m : ℕ) (hm : 0 < m) :
    UniversalScalingLaw.dBal (UniversalScalingLaw.α m) (m + 1) = 0 ∧
    0 < UniversalScalingLaw.dBal (UniversalScalingLaw.α m) m ∧
    SpectralGeometric.root_amplitude_sq m *
      ChristoffelDarboux.quantum_dim_sq m = 1 :=
  ⟨UniversalScalingLaw.dBal_vanishes_at_threshold m hm,
   UniversalScalingLaw.dBal_minor_pos_at_threshold m hm,
   UniversalScalingLaw.cd_norm m⟩

/--
The ratio computation that feeds the universal `-1` coefficient in the
tridiagonal/Chebyshev route.
-/
theorem appendixC_hankel_bridge_ratio (m : ℕ) (hm : 0 < m)
    (hd : ClosedFormDet.d (HankelBridge.α m) (m + 1) = 0)
    (hdd : HankelBridge.d_deriv (HankelBridge.α m) (m + 1) ≠ 0) :
    (ClosedFormDet.d (HankelBridge.α m) m /
        HankelBridge.d_deriv (HankelBridge.α m) (m + 1)) *
      (ChristoffelDarboux.quantum_dim_sq m / 2) = 1 :=
  HankelBridge.full_bridge m hm hd hdd

/--
The no-input canonical Appendix C scaling endpoint.

For every `m > 0`, there exists a smooth local branch `ψ` with
`ψ(0)=α_m`, `ψ'(0)=-1`, and
`ψ(1/d₁²)d₁ = α_m d₁ - 1/d₁ + O(d₁^{-3})`.

This is the canonical engineered branch from `PhysicalScalingLaw`; it is not the
all-`m` physical determinant statement for `detB_m`.  The actual physical
determinant is exposed below only in the checked small cases `m = 1,2,3`.
-/
theorem appendixC_canonical_universal_scaling_law :
    ∀ m : ℕ, 0 < m →
      ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
        0 < D₀ ∧ ψ 0 = SelfContainedProof.α m ∧ HasDerivAt ψ (-1) 0 ∧
        (∀ d₁ : ℝ, D₀ < d₁ →
          |ψ (1 / d₁ ^ 2) * d₁ - (SelfContainedProof.α m * d₁ - 1 / d₁)|
            ≤ C / d₁ ^ 3) :=
  PhysicalScalingLaw.canonical_universal_scaling_law

/--
Self-contained tridiagonal scaling theorem from `UniversalScalingLawProof`.

This exposes the fully checked Chebyshev/implicit-function route in this
Appendix C consolidation file: the balanced determinant vanishes, the adjacent
minor is positive, and a local threshold branch satisfies the stated
`O(d₁^{-3})` expansion.
-/
theorem appendixC_self_contained_tridiagonal_scaling_law (m : ℕ) (hm : 0 < m) :
    UniversalScalingLaw.dBal (UniversalScalingLaw.α m) (m + 1) = 0 ∧
    0 < UniversalScalingLaw.dBal (UniversalScalingLaw.α m) m ∧
      ∃ ψ C D,
        0 < D ∧
          ψ 0 = UniversalScalingLaw.α m ∧
            (∀ᶠ δ in nhds 0,
              ClosedFormDet.d (ψ δ) (m + 1) = δ * ClosedFormDet.d (ψ δ) m) ∧
              HasDerivAt ψ (RemainderBound.first_order_coeff m) 0 ∧
                ∀ d₁ : ℝ, D < d₁ →
                  |ψ (1 / d₁ ^ 2) * d₁ -
                    (UniversalScalingLaw.α m * d₁ +
                      RemainderBound.first_order_coeff m / d₁)| ≤ C / d₁ ^ 3 :=
  UniversalScalingLawProof.complete m hm

/--
The checked second-order sharpness statement accompanying the self-contained
tridiagonal scaling proof.
-/
theorem appendixC_self_contained_tridiagonal_sharpness :
    RemainderBound.second_order_coeff 1 = 0 ∧
      ∀ m : ℕ, 2 ≤ m → 0 < RemainderBound.second_order_coeff m :=
  UniversalScalingLawProof.sharpness

end ChebyshevTridiagonalSpine

section ConcretePhysicalCases

/--
The actual physical determinant route is checked for `m = 1`.
-/
theorem appendixC_physical_scaling_law_m1 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = SelfContainedProof.α 1 ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (SelfContainedProof.α 1 * d₁ - 1 / d₁)|
          ≤ C / d₁ ^ 3) :=
  PhysicalScalingLaw.physical_scaling_law_m1

/--
The actual physical determinant route is checked for `m = 2`.
-/
theorem appendixC_physical_scaling_law_m2 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = SelfContainedProof.α 2 ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (SelfContainedProof.α 2 * d₁ - 1 / d₁)|
          ≤ C / d₁ ^ 3) :=
  PhysicalScalingLaw.physical_scaling_law_m2

/--
The actual physical determinant route is checked for `m = 3`.
-/
theorem appendixC_physical_scaling_law_m3 :
    ∃ ψ : ℝ → ℝ, ∃ C D₀ : ℝ,
      0 < D₀ ∧ ψ 0 = SelfContainedProof.α 3 ∧ HasDerivAt ψ (-1) 0 ∧
      (∀ d₁ : ℝ, D₀ < d₁ →
        |ψ (1 / d₁ ^ 2) * d₁ - (SelfContainedProof.α 3 * d₁ - 1 / d₁)|
          ≤ C / d₁ ^ 3) :=
  PhysicalScalingLaw.physical_scaling_law_m3

end ConcretePhysicalCases

end AppendixCMainResult
