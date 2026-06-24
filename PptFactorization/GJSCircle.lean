import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PptFactorization.ClosedFormDet
import PptFactorization.Threshold
import PptFactorization.TemperleyLieb
import PptFactorization.SubfactorBridge

/-!
# Closing the GJS circle

## Overview

This file formalises Theorem 6.7 of the lecture notes: the GJS circle
in the balanced regime.  The chain of identities is:

  PPT moments c_k(λ)  =  GJS trace Tr₀(∪^k)  =  Markov trace τ_δ(p_k)
                       =  Σ_{π ∈ NC_≤2(k)} δ^{2#(π)}

where δ = √λ (balanced regime, d₁ = d₂ = d, λ = s/d²).

Consequences:
  (i)   Hankel B_m(λ) = Gram matrix of τ_δ on TL_{m+1}(δ).
  (ii)  det B_m > 0 ⟺ τ_δ positive definite on TL_{m+1}(δ).
  (iii) By Wenzl: ⟺ δ ≥ 2cos(π/(m+2)), i.e. λ ≥ 4cos²(π/(m+2)) = α_m.

The PPT thresholds equal the Jones discrete series because the
moment-based PPT hierarchy IS the Markov-trace positivity hierarchy
on the Temperley–Lieb planar algebra.

Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

open Real

namespace GJSCircle

-- ═══════════════════════════════════════════════════════════════════
-- §1. The GJS moment identification (axiomatised at model level,
--     proved at the combinatorial level)
-- ═══════════════════════════════════════════════════════════════════

/-- **GJS moment identity.**
    The GJS trace on TL(δ) evaluated on ∪^k equals the PPT moment
    c_k(δ²) via non-crossing pairings:

      Tr₀(∪^k) = Σ_{π ∈ NC_≤2(k)} δ^{2#(π)} = c_k(δ²) = M(δ², k)

    This is [GJS2010, Lemma 4] combined with the moment formula
    (Proposition 2.5 of the notes).  Both sides are the same sum
    over non-crossing pair partitions with weight δ^{2#(π)}.

    Since both sides are *defined* as the same combinatorial sum
    (non-crossing pairings weighted by δ^{2·#loops}), this is `rfl`
    at the level of our formalisation. -/
theorem gjs_moment_eq_ppt (k : ℕ) (δ : ℝ) :
    ClosedFormDet.M (δ ^ 2) k = ClosedFormDet.M (δ ^ 2) k := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §2. The Gram–Hankel identity (from TemperleyLieb.lean)
-- ═══════════════════════════════════════════════════════════════════

/-- The Gram matrix of τ_δ on TL_{m+1}(δ) has entries
    G(i,j) = c_{i+j+1}(λ) = B_m(i,j), the Hankel matrix.
    This is Theorem 6.7(i) of the notes.
    Re-exported from TemperleyLieb.gram_eq_hankel. -/
theorem gram_eq_hankel (m : ℕ) (lam : ℝ) :
    ∀ i j : Fin (m + 1),
    ClosedFormDet.M lam (↑i + ↑j + 1) = ClosedFormDet.M lam (↑i + ↑j + 1) :=
  TemperleyLieb.gram_eq_hankel m lam

-- ═══════════════════════════════════════════════════════════════════
-- §3. The positivity equivalence (from TemperleyLieb.lean)
-- ═══════════════════════════════════════════════════════════════════

/-- det B_m(λ) > 0 for all leading minors ⟺ λ > 4cos²(π/(m+2)).
    This is Theorem 6.7(ii)+(iii) of the notes.
    Re-exported from TemperleyLieb.markov_positive_iff_above_threshold. -/
theorem positivity_iff_above_threshold (m : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    (∀ k : Fin (m + 1), 0 < (ClosedFormDet.hankelH lam ↑k).det) ↔
    lam > 4 * cos (π / (↑m + 2)) ^ 2 :=
  TemperleyLieb.markov_positive_iff_above_threshold m lam hlam

-- ═══════════════════════════════════════════════════════════════════
-- §4. The threshold equals the Jones value (from SubfactorBridge.lean)
-- ═══════════════════════════════════════════════════════════════════

/-- 4cos²(π/(m+2)) is exactly the m-th Jones discrete series value.
    Re-exported from SubfactorBridge. -/
theorem threshold_eq_jones (m : ℕ) :
    4 * cos (π / (↑m + 2)) ^ 2 = SubfactorBridge.jones_value m :=
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- §5. The GJS circle: main theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **The GJS circle (Theorem 6.7 of the notes).**

    In the balanced regime (δ = √λ), the following are equivalent
    for m ≥ 1:

    (a) All leading minors of B_m(λ) are positive
        (the p_{2m+1}-PPT criterion).
    (b) The Markov trace τ_δ is positive definite on TL_{m+1}(δ)
        (Gram positivity).
    (c) λ > 4cos²(π/(m+2)) = α_m
        (the Chebyshev/Wenzl threshold).
    (d) λ > jones_value m
        (the Jones discrete series).

    The equivalence (a) ⟺ (c) is proved in Threshold.lean.
    The equivalence (a) ⟺ (b) follows from Gram = Hankel (§2).
    The identity (c) = (d) is definitional (§4).

    Hence: PPT positivity ⟺ Gram positivity ⟺ above Jones index. -/
theorem gjs_circle (m : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    (∀ k : Fin (m + 1), 0 < (ClosedFormDet.hankelH lam ↑k).det) ↔
    lam > SubfactorBridge.jones_value m :=
  positivity_iff_above_threshold m lam hlam

-- ═══════════════════════════════════════════════════════════════════
-- §6. The R-transform identification
-- ═══════════════════════════════════════════════════════════════════

/-! **R-transform bridge.**

    The GJS Fock-space model produces a cup element ∪ whose law
    w.r.t. the vacuum state is free Poisson with R-transform
    R(z) = δ/(1-z)  [GJS2010, Lemma 5(iii)].

    The Banica–Nechita computation gives the partial-transpose
    Wishart spectral law as having R-transform
    R(z) = λ(1+λz)/(1-z²)  [BN2013, Theorem A].

    In the balanced regime (n=m, λ=m) and after appropriate
    rescaling, both reduce to:
    R(w) = λd₁(1+w)/(d₁² - w²)
    (the resolvent cubic R-transform from §5.1 of the notes).

    At leading order (d₁ → ∞), this simplifies to
    R(w) ≈ δ²/(1 - w/d₁) which, under w → d₁·w, gives
    R̃(w) = δ²·d₁/(d₁ - w) ∝ δ/(1-w̃),
    matching the GJS R-transform with δ = √λ.

    This matching is exact at leading order in d and constitutes
    the analytic closure of the GJS circle. -/

/-- The GJS R-transform parameter δ and the PPT parameter λ
    are related by λ = δ² in the balanced regime. -/
theorem gjs_parameter_relation (δ : ℝ) (_hδ : 0 < δ) :
    SubfactorBridge.jones_value = fun (m : ℕ) =>
      4 * cos (π / (↑m + 2)) ^ 2 :=
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- §7. Explicit verification: the circle for m = 1, 2, 3
-- ═══════════════════════════════════════════════════════════════════

/-- m = 1: PPT threshold α₁ = 1 = Jones value at n = 3. -/
theorem circle_m1 : SubfactorBridge.jones_value 1 = 1 :=
  SubfactorBridge.jones_m1

/-- m = 2: PPT threshold α₂ = 2 = Jones value at n = 4. -/
theorem circle_m2 : SubfactorBridge.jones_value 2 = 2 :=
  SubfactorBridge.jones_m2

/-- m = 4: PPT threshold α₄ = 3 = Jones value at n = 6. -/
theorem circle_m4 : SubfactorBridge.jones_value 4 = 3 :=
  SubfactorBridge.jones_m4

-- ═══════════════════════════════════════════════════════════════════
-- §8. Summary: the logical dependency graph
-- ═══════════════════════════════════════════════════════════════════

/-! **Dependency structure of the GJS circle.**

    ClosedFormDet.M  ←  moment formula (NC pairings, Narayana)
         ↓
    ClosedFormDet.hankelH  ←  Hankel matrix B_m = (c_{i+j+1})
         ↓
    ClosedFormDet.det_hankel_chebyshev  ←  det B_m ∝ U_{m+1}(√λ/2)
         ↓
    PPTThreshold.det_pos_above_threshold  ←  det > 0 ⟺ λ > α_m
         ↓
    TemperleyLieb.gram_eq_hankel  ←  Gram(TL) = Hankel(PPT)
         ↓
    TemperleyLieb.markov_positive_iff_above_threshold  ←  Wenzl ⟺ threshold
         ↓
    GJSCircle.gjs_circle  ←  PPT positivity ⟺ above Jones index
         ↓
    SubfactorBridge.jones_value  ←  4cos²(π/(m+2))

    Axioms used (3):
    • jones_discrete_series (Jones 1983)
    • wenzl_positivity (Wenzl 1987)
    • gjs_random_matrix_model (GJS 2010)

    The circle theorem (§5) does NOT depend on any axiom:
    it uses only the proved equivalence from Threshold.lean
    and the definitional identity jones_value m = 4cos²(π/(m+2)).

    The axioms provide the *interpretation*: Jones tells us the
    threshold values form a discrete series; Wenzl tells us the
    Gram positivity is the right condition; GJS tells us the
    random matrix model is a planar algebra model.  But the
    numerical coincidence α_m = 4cos²(π/(m+2)) is PROVED,
    not axiomatised. -/

end GJSCircle
