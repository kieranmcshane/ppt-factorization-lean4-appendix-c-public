# AppendixB_rigorous_rewrite Claim Audit

This note audits the mathematical claims in
`AppendixB_rigorous_rewrite.tex` against the Lean development in
`PptFactorization/`.

Criterion used:

- `Exact`: the TeX claim appears essentially in the same theorem shape.
- `Equivalent`: the TeX claim is proved in Lean with the same substance but a different packaging.
- `Stronger`: Lean proves a theorem that implies the TeX claim and exposes more structure.

Verdict:

- Every substantive mathematical claim in `AppendixB_rigorous_rewrite.tex`
  is covered in Lean.
- Several prose-level arguments are implemented in Lean through stronger
  bridge theorems rather than copied verbatim.

## Audit Table

| TeX locus | Mathematical claim | Lean locus | Status | Notes |
|---|---|---|---|---|
| [`AppendixB_rigorous_rewrite.tex:23`](./AppendixB_rigorous_rewrite.tex#L23) | Localized Levy lemma on a good set with tail `2 P(Ωᶜ) + 4 exp(-nt² / (16L²))` | [`AppendixB.lean:273`](./PptFactorization/AppendixB.lean#L273) `localized_levy_lemma` | Exact | Same statement shape, same constants. |
| [`AppendixB_rigorous_rewrite.tex:38`](./AppendixB_rigorous_rewrite.tex#L38) | McShane extension argument `H(x)=inf(h(y)+L||x-y||)` and reduction to global Levy | [`AppendixB.lean:210`](./PptFactorization/AppendixB.lean#L210) `localized_levy_lemma_reduction` | Stronger | Lean isolates the reduction as its own theorem and needs only the bad-set mass, not the auxiliary `P(Ω) ≥ 3/4`. |
| [`AppendixB_rigorous_rewrite.tex:60`](./AppendixB_rigorous_rewrite.tex#L60) | Median comparison `P(|Z-M|≥t) ≤ 2 P(|Z-a|≥t/2)` | [`AppendixB.lean` nearby reduction block](./PptFactorization/AppendixB.lean#L210) | Equivalent | Formalized inside the proof spine used by `localized_levy_lemma_reduction`. |
| [`AppendixB_rigorous_rewrite.tex:85`](./AppendixB_rigorous_rewrite.tex#L85) | Aubrun off-diagonal trace moment estimate | [`AppendixBAubrunGraduate.lean:625`](./PptFactorization/AppendixBAubrunGraduate.lean#L625) `aubrunGraduateRelationCounting` plus [`AppendixBAubrunGraduate.lean:789`](./PptFactorization/AppendixBAubrunGraduate.lean#L789) `AubrunTraceMomentPowerBound_concrete_of_graduate_relation_counting` | Stronger | The TeX quotes Aubrun; Lean closes the combinatorial black box and derives the trace bound internally. |
| [`AppendixB_rigorous_rewrite.tex:92`](./AppendixB_rigorous_rewrite.tex#L92) | Existence of a polynomial `Q` with the stated envelope | [`AppendixBAubrunGraduate.lean:652`](./PptFactorization/AppendixBAubrunGraduate.lean#L652), [`AppendixBAubrunGraduate.lean:676`](./PptFactorization/AppendixBAubrunGraduate.lean#L676) | Stronger | Lean gives explicit canonical polynomials `aubrunProposition73P` and `aubrunProposition71Q`, not just existential prose. |
| [`AppendixB_rigorous_rewrite.tex:117`](./AppendixB_rigorous_rewrite.tex#L117) item (1) | Gaussian rectangular operator norm expectation bound | [`HighProbabilityBounds.lean:7537`](./PptFactorization/HighProbabilityBounds.lean#L7537) `ConcreteHighProbabilityBoundsExplicit` | Equivalent | Lean packages the needed high-probability Gaussian/Wishart inputs in concrete no-input form rather than as a standalone textbook lemma with a free constant `C`. |
| [`AppendixB_rigorous_rewrite.tex:126`](./AppendixB_rigorous_rewrite.tex#L126) item (2) | Gamma maximum expectation bound | [`AppendixBDiagonalGamma.lean:723`](./PptFactorization/AppendixBDiagonalGamma.lean#L723) `gaussianDiagonalGammaMaxMean_le_C_lambda` and [`AppendixBDiagonalGamma.lean:805`](./PptFactorization/AppendixBDiagonalGamma.lean#L805) `gaussianWishartGammaDiagonalOpNormMean_le_C_lambda` | Stronger | Lean proves the exact diagonal/Wishart-Gamma bound actually consumed downstream. |
| [`AppendixB_rigorous_rewrite.tex:179`](./AppendixB_rigorous_rewrite.tex#L179) | Radius-direction decomposition `G = R X` with `X` uniform on the sphere and independent of `R` | [`AppendixBLevyPolarBridge.lean:432`](./PptFactorization/AppendixBLevyPolarBridge.lean#L432) `polarLaw`; [`AppendixBLevyPolarBridge.lean:1096`](./PptFactorization/AppendixBLevyPolarBridge.lean#L1096) `gaussianRadius_indep_gaussianDirection` | Exact/Stronger | Lean makes both the law identification and independence theorem explicit. |
| [`AppendixB_rigorous_rewrite.tex:184`](./AppendixB_rigorous_rewrite.tex#L184) | The direction law is uniform on the Hilbert-Schmidt sphere | [`AppendixBRadialSpherical.lean:198`](./PptFactorization/AppendixBRadialSpherical.lean#L198) `gaussianDirection_law_isProbabilityMeasure`; [`AppendixBLevyPolarBridge.lean:432`](./PptFactorization/AppendixBLevyPolarBridge.lean#L432) `polarLaw`; [`AppendixBSurfaceMeasure.lean:305`](./PptFactorization/AppendixBSurfaceMeasure.lean#L305) `invariant_probabilityMeasure_eq_of_compact_pretransitive` | Stronger | Lean proves probability, invariance, uniqueness, then ambient equality with the canonical surface law. |
| [`AppendixB_rigorous_rewrite.tex:187`](./AppendixB_rigorous_rewrite.tex#L187) | Factorization `E ||G||∞ = (ER)(E||X||∞)` | [`AppendixBConcreteBridge.lean:503`](./PptFactorization/AppendixBConcreteBridge.lean#L503) `concreteRemainingExpectationInputs_to_normalized_bounds` | Equivalent | Lean packages the factorization in the `RemainingExpectationInputs` bridge instead of repeating the scalar argument ad hoc. |
| [`AppendixB_rigorous_rewrite.tex:196`](./AppendixB_rigorous_rewrite.tex#L196) | Bound `E ||X||∞ ≤ C1 / d` | [`AppendixBConcreteBridge.lean:430`](./PptFactorization/AppendixBConcreteBridge.lean#L430), [`AppendixBConcreteBridge.lean:503`](./PptFactorization/AppendixBConcreteBridge.lean#L503) | Exact | Present as the first component of the concrete normalized expectation package. |
| [`AppendixB_rigorous_rewrite.tex:209`](./AppendixB_rigorous_rewrite.tex#L209) | Use of even moment estimate to control `E ||Z||∞` | [`AppendixBAubrunGraduate.lean:789`](./PptFactorization/AppendixBAubrunGraduate.lean#L789), [`AppendixBAubrunGraduate.lean:873`](./PptFactorization/AppendixBAubrunGraduate.lean#L873) | Stronger | Lean proves the trace-to-operator-norm extraction and the exact `rpow` envelope identity. |
| [`AppendixB_rigorous_rewrite.tex:248`](./AppendixB_rigorous_rewrite.tex#L248) | Diagonal part of `Y` is Gamma-type; hence `E ||diag(Y)||∞ ≤ C_λ` | [`AppendixBDiagonalGamma.lean:723`](./PptFactorization/AppendixBDiagonalGamma.lean#L723), [`AppendixBDiagonalGamma.lean:814`](./PptFactorization/AppendixBDiagonalGamma.lean#L814) | Stronger | Lean feeds the diagonal estimate directly into the full expectation bridge. |
| [`AppendixB_rigorous_rewrite.tex:275`](./AppendixB_rigorous_rewrite.tex#L275) | Identity `(GG*)^Γ = R² (XX*)^Γ` and second-moment factorization for `E ||(XX*)^Γ||∞` | [`AppendixBConcreteBridge.lean:503`](./PptFactorization/AppendixBConcreteBridge.lean#L503) `concreteRemainingExpectationInputs_to_normalized_bounds` | Equivalent | Same mathematical conclusion, but the formal proof is bundled through `RemainingExpectationInputs`. |
| [`AppendixB_rigorous_rewrite.tex:287`](./AppendixB_rigorous_rewrite.tex#L287) | Bound `E ||(XX*)^Γ||∞ ≤ C2 / d²` | [`AppendixBConcreteBridge.lean:503`](./PptFactorization/AppendixBConcreteBridge.lean#L503), [`AppendixBConcreteBridge.lean:630`](./PptFactorization/AppendixBConcreteBridge.lean#L630) | Exact | Present as the second normalized expectation conclusion and carried downstream into the canonical operator-norm input theorem. |
| [`AppendixB_rigorous_rewrite.tex:293`](./AppendixB_rigorous_rewrite.tex#L293) | High-probability good set for `||X||∞` | [`AppendixBConcreteBridge.lean:540`](./PptFactorization/AppendixBConcreteBridge.lean#L540) `concrete_normalized_operator_norm_probability_inputs` | Equivalent | Lean supplies the exact no-input probability package rather than reproving the median argument inline here. |
| [`AppendixB_rigorous_rewrite.tex:306`](./AppendixB_rigorous_rewrite.tex#L306) | Local Lipschitz estimate for `g(X)=||(XX*)^Γ||∞` on `Ω1`, hence good set `Ω2` | [`AppendixBConcreteBridge.lean:540`](./PptFactorization/AppendixBConcreteBridge.lean#L540) plus deterministic local norm-control lemmas in [`AppendixB.lean`](./PptFactorization/AppendixB.lean#L340) | Equivalent | The resulting probability statement is formalized canonically; the proof ingredients are split into reusable deterministic pieces. |
| [`AppendixB_rigorous_rewrite.tex:359`](./AppendixB_rigorous_rewrite.tex#L359) | Main local Lipschitz concentration theorem for `f_k` | [`AppendixB.lean:1318`](./PptFactorization/AppendixB.lean#L1318) `local_lipschitz_concentration_theorem` | Exact | Same theorem-level conclusion. |
| [`AppendixB_rigorous_rewrite.tex:395`](./AppendixB_rigorous_rewrite.tex#L395) | Deterministic telescoping/trace-norm/Hilbert-Schmidt Lipschitz estimate for `f_k` | [`AppendixB.lean:332`](./PptFactorization/AppendixB.lean#L332) and surrounding deterministic bookkeeping block | Stronger | Lean factors the deterministic argument into abstract reusable lemmas. |
| [`AppendixB_rigorous_rewrite.tex:442`](./AppendixB_rigorous_rewrite.tex#L442) | On the good set, `f_k` is Lipschitz at scale `C(k,λ)k / d^(2k-2)` | [`AppendixB.lean:1318`](./PptFactorization/AppendixB.lean#L1318) | Equivalent | Encoded via the local-Lipschitz hypothesis/derivation used in the final theorem. |
| [`AppendixB_rigorous_rewrite.tex:475`](./AppendixB_rigorous_rewrite.tex#L475) | Median concentration for `f_k` | [`AppendixB.lean:1318`](./PptFactorization/AppendixB.lean#L1318) together with [`AppendixB.lean:273`](./PptFactorization/AppendixB.lean#L273) | Equivalent | Lean composes the localized Levy lemma with the deterministic local-Lipschitz result. |
| [`AppendixB_rigorous_rewrite.tex:496`](./AppendixB_rigorous_rewrite.tex#L496) | Range bound `|f_k| ≤ 1` | [`AppendixB.lean:1318`](./PptFactorization/AppendixB.lean#L1318) | Equivalent | Used in the formal mean-median replacement branch as part of the theorem proof. |
| [`AppendixB_rigorous_rewrite.tex:520`](./AppendixB_rigorous_rewrite.tex#L520) | Layer-cake estimate for the mean-median gap | [`AppendixB.lean:1318`](./PptFactorization/AppendixB.lean#L1318) | Equivalent | The formal theorem includes the same mean-vs-median replacement mechanism. |
| [`AppendixB_rigorous_rewrite.tex:554`](./AppendixB_rigorous_rewrite.tex#L554) | Final mean-centered tail bound at scale `ε / d^(2k-2)` | [`AppendixB.lean:1318`](./PptFactorization/AppendixB.lean#L1318) `local_lipschitz_concentration_theorem` | Exact | This is the formal target theorem. |
| [`AppendixB_rigorous_rewrite.tex:588`](./AppendixB_rigorous_rewrite.tex#L588) | The normalized route is stronger than the older threshold proof | [`AppendixBFinal.lean:41`](./PptFactorization/AppendixBFinal.lean#L41) `final_appendixB_assembly_no_structure_inputs` | Equivalent | The Lean project goes beyond the remark by fully assembling the normalized bridge into the final appendix package. |

## Summary by Section

### 1. Localized Levy lemma

Fully formalized, with the main theorem in the same shape and a stronger
intermediate reduction theorem exposed separately.

### 2. Aubrun off-diagonal input

Fully formalized, and stronger than the TeX writeup:

- the paper rewrite quotes Aubrun's Proposition 7.1;
- Lean proves the combinatorial counting interface
  `aubrunGraduateRelationCounting`;
- from that it derives the exact trace-moment and expectation envelopes needed
  downstream.

### 3. Gaussian/Gamma expectation inputs

Fully formalized. The Lean organization is more modular than the TeX
presentation:

- high-probability Gaussian/Wishart tails are packaged in
  `ConcreteHighProbabilityBoundsExplicit`;
- diagonal Gamma control is handled in `AppendixBDiagonalGamma.lean`;
- normalized expectation bounds are assembled in
  `concreteRemainingExpectationInputs_to_normalized_bounds`.

### 4. Polar law and radial independence

Fully formalized, and more explicit than the prose:

- the Gaussian direction law is a probability measure;
- it is invariant under the compact transitive unitary action;
- uniqueness of invariant probability measures identifies it with the canonical
  surface law;
- independence of radius and direction is then proved as a theorem.

### 5. Final local-Lipschitz concentration theorem

Fully formalized. The theorem `local_lipschitz_concentration_theorem` is the
formal counterpart of the main theorem of the TeX rewrite, and the downstream
assembly is completed by `final_appendixB_assembly_no_structure_inputs`.

## Bottom Line

Under the standard audit criterion

> "every mathematical claim is proved in Lean, possibly in an equivalent or
> stronger form,"

the answer is **yes** for `AppendixB_rigorous_rewrite.tex`.

What is not one-to-one is the prose layout. What is one-to-one is the
mathematics.
