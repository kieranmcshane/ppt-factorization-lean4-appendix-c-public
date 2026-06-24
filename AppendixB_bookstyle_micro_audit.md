# Appendix B Book-Style Draft: Micro-Audit Against Lean

Source audited: `AppendixB_bookstyle.tex`.

This audit is intentionally smaller-grain than the previous concordance.  It
does not ask whether a theorem belongs to the right *family*.  It asks whether
the displayed mathematical statement in the book-style draft is matched by a
Lean theorem with the same conclusion and the same hypotheses, or by a formally
stronger theorem whose extra hypotheses are already discharged in Lean.

## Status Legend

- **PASS-exact**: displayed statement matches a Lean conclusion with matching
  hypotheses.
- **PASS-stronger**: Lean proves a stronger or more explicit statement from
  which the displayed statement follows without new mathematics.
- **PASS-conditional**: Lean proves the displayed statement only after an
  explicit input hypothesis.  The book statement must either expose that
  hypothesis or cite a separate Lean theorem discharging it.
- **TEXT-gap**: the mathematics is likely correct, but the prose statement is
  missing a definition, quantifier, measurability, integrability, positivity,
  dimension, or domain hypothesis.
- **LEAN-gap**: the book asserts a theorem that is not currently matched by a
  no-input Lean theorem with the same hypotheses.

Variable-classification codes:

- **D** = defined earlier in prose.
- **Q** = quantified in the displayed statement.
- **M** = measurability hypothesis.
- **I** = integrability or finite-expectation hypothesis.
- **N** = nonnegativity, positivity, or dimension lower-bound hypothesis.
- **Der** = derived in the proof from earlier facts.
- **Hidden** = used but not stated locally.

Analytic theorem checks list only nontrivial analytic invocations: polar
coordinates, Haar uniqueness, Levy concentration, McShane extension, layer
cake, Chernoff bounds, Gaussian comparison, Paley--Zygmund/Gamma estimates,
tail integration, and independence/product integration.

## First-Definition Audit

| Term introduced in prose | First occurrence | First-definition status | Action |
|---|---:|---|---|
| finite-dimensional complex Hilbert spaces | Norm definition | Partly defined by context only | Add a sentence identifying the vector norm `\|v\|_2` as the Hilbert norm induced by the inner product. |
| operator norm | Definition at line 108 | Defined explicitly | OK. |
| Hilbert--Schmidt norm | Definition at line 108 | Defined explicitly | OK. |
| trace norm/Schatten 1-norm | Definition at line 108 | Defined explicitly | OK. |
| partial transpose `A^{\GammaPT}` | Section line 155 | Defined explicitly on coordinates | OK. |
| standard complex Gaussian | Section line 198 | Defined explicitly; exponential law stated | OK. |
| Gamma distribution shape/scale | Section line 198 | Used but not defined | Add convention: density `x^{r-1}e^{-x}/Gamma(r)` for scale 1. |
| normalized surface measure | Polar law section | Named but not constructed | Add definition as normalized Hausdorff/spherical measure on the Hilbert--Schmidt unit sphere. |
| median | Definition at line 340 | Defined explicitly | OK. |
| Levy's lemma / spherical Levy inequality | Theorem line 387 | Statement clear, but “Levy” has accent inconsistency only | OK after changing phrase to “spherical concentration inequality.” |
| McShane extension | Localized Levy proof | Used but not defined | Add one sentence: for an `L`-Lipschitz function on a subset of a metric space, the displayed infimum is an `L`-Lipschitz extension. |
| Wick formula | Theorem line 609 | Defined by statement | OK. |
| surviving Wick permutation | Definition line 677 | Defined explicitly | OK. |
| relation profile | Definition line 748 | Defined explicitly | OK. |
| tilde words/list (3)/list (7) | Section line 767 | Informal, not fully first-defined | The book needs a displayed definition if it wants 1-1 correspondence with Lean objects. |
| innovation | Section line 767 | Informal, not formally specified | Needs a precise scan order and equivalence-class rule. |
| compatibility defect | Section line 767 | Informal | Needs a displayed definition or a reference to a precise definition. |
| off-diagonal part `Z` | Section line 633 and 854 | Defined | OK. |
| constants `C_\lambda`, `c`, `C` | Many theorems | Usually quantified existentially or by prose | OK when quantified; otherwise state dependence explicitly. |

## Displayed Statement Audit Rows

### B-01. Definition: Operator, Hilbert--Schmidt, and Trace Norms

- **Source**: `AppendixB_bookstyle.tex:108`.
- **Variables**: `E,F` finite-dimensional complex Hilbert spaces (**Q**);
  `T:E -> F` linear (**Q**); vector norm `\|\cdot\|_2` (**Hidden/D**, should
  be defined); adjoint `T^*` (**D** if Hilbert spaces have inner products).
- **Analytic proof-step checks**: none.
- **Lean counterpart**: `PptFactorization/RandomMatrixModel.lean` defines
  `frobeniusNorm`; operator norm is handled through `opNorm` and matrix norm
  APIs.  Trace norm is used through finite-dimensional Schatten/nuclear norm
  inequalities rather than as one standalone definition.
- **Conclusion/hypotheses match**: conceptual match, but not one theorem.
- **Verdict**: **PASS-stronger + TEXT-gap**.  Lean has enough finite matrix
  norm infrastructure; the prose should define `\|v\|_2` before using it.

### B-02. Lemma: Basic Norm Facts

- **Source**: `AppendixB_bookstyle.tex:167`.
- **Variables**: `A in M_I(C)` (**Q**); `I=P x Q`, `D=|I|` (**D**);
  `m` even (**Q+N**); `A` Hermitian for last inequality (**Q**).
- **Analytic proof-step checks**: singular value inequalities require finite
  dimension (**D**); spectral theorem for Hermitian matrix (**D**); partial
  transpose coordinate permutation (**D**).
- **Lean counterpart**:
  - `RandomMatrixModel.lean`: `frobeniusNorm_gamma`.
  - `HighProbabilityBounds.lean` / norm lemmas: operator norm bounded by
    Frobenius norm, trace/Frobenius comparisons.
  - `AppendixB.lean`: even trace-power extraction uses the Hermitian/even
    power inequality downstream.
- **Conclusion/hypotheses match**: first two inequalities match; trace-norm
  comparison and even-power inequality are used/formalized in the finite
  matrix setting.
- **Verdict**: **PASS-stronger**.

### B-03. Theorem: Gaussian Polar Law

- **Source**: `AppendixB_bookstyle.tex:272`.
- **Variables**: `G` standard complex Gaussian in `X=M_{I,Sigma}(C)` (**D**);
  `R(G)=||G||_HS` (**D**); `Theta(G)=G/||G||_HS` off zero (**D**);
  `sigma_X` normalized surface measure (**D but needs construction**);
  nonempty finite index sets (**Hidden/N**).
- **Analytic proof-step checks**: polar-coordinate Jacobian requires real
  dimension `2DS >= 1` (**Hidden/N**); zero has Gaussian mass zero (**Der**);
  angular marginal normalized (**Der**); product density implies independence
  (**analytic theorem: product-law criterion; hypotheses need measurability of
  `R` and `Theta`, derived from continuity away from zero plus null-zero
  convention).
- **Lean counterpart**:
  - `AppendixBRadialSpherical.lean`: `gaussianDirection_law_isProbabilityMeasure`,
    `gaussianDirection_law_map_complexLinearIsometryEquiv`.
  - `AppendixBLevyPolarBridge.lean`: `polarLaw` proves
    `sphericalModelMeasure = surfaceModelMeasure`.
  - `AppendixBLevyPolarBridge.lean`: `gaussianRadius_indep_gaussianDirection`.
  - `AppendixBSurfaceMeasure.lean`: `invariant_probabilityMeasure_eq_of_compact_pretransitive`.
- **Conclusion/hypotheses match**: Lean proves the angular-law equality by
  compact-unitary invariance and Haar uniqueness, and separately proves
  radius-direction independence.  This is equivalent to the displayed
  conclusion, but the proof route is not the same as the prose polar-coordinate
  proof.
- **Verdict**: **PASS-stronger + TEXT-gap**.  Add explicit nonempty finite
  index hypotheses and a definition/construction of normalized surface measure.

### B-04. Remark: Invariant Characterization of the Direction Law

- **Source**: `AppendixB_bookstyle.tex:304`.
- **Variables**: unitary group `U(X)` (**D but not constructed**); sphere
  action (**Hidden**); direction law (**D**); surface law (**D**).
- **Analytic proof-step checks**: unitary invariance of Gaussian; equivariance
  of normalization; compactness/transitivity of unitary action; regularity and
  probability of both measures; Haar uniqueness.
- **Lean counterpart**:
  - `AppendixBSurfaceMeasure.lean`: `invariant_probabilityMeasure_eq_of_compact_pretransitive`.
  - `AppendixBLevyPolarBridge.lean`: surface-law invariance and
    Gaussian-direction-law invariance are fed to that uniqueness theorem.
- **Conclusion/hypotheses match**: yes, with regularity/probability/compact
  hypotheses explicit in Lean.
- **Verdict**: **PASS-exact as proof route**, but the book should not leave
  regularity/probability implicit if this remark is part of the audit trail.

### B-05. Corollary: Radial Rescalings

- **Source**: `AppendixB_bookstyle.tex:313`.
- **Variables**: `G != 0` (**Q/N**); `R`, `Theta`, `GammaPT` (**D**).
- **Analytic proof-step checks**: none beyond algebra; norm scaling by
  nonnegative scalar `R` and `R^2` (**Der/N**).
- **Lean counterpart**:
  - `AppendixBRadialSpherical.lean`: pointwise radial identities such as
    `gaussian_sampleOpNorm_pointwise_radial` and quadratic radial/spherical
    factorization lemmas.
- **Conclusion/hypotheses match**: yes, Lean has the pointwise identities
  used to derive expectation factorization.
- **Verdict**: **PASS-stronger**.

### B-06. Definition: Median

- **Source**: `AppendixB_bookstyle.tex:340`.
- **Variables**: probability space `(Omega,mu)` (**D**); measurable
  `f:Omega -> R` (**D/M**); `m in R` (**Q**).
- **Analytic proof-step checks**: sets `{f <= m}` and `{f >= m}` measurable
  require `f` measurable (**M**).
- **Lean counterpart**: `AppendixB.lean`: `_root_.AppendixB.IsMedian`.
- **Conclusion/hypotheses match**: yes.
- **Verdict**: **PASS-exact**.

### B-07. Lemma: Changing the Center

- **Source**: `AppendixB_bookstyle.tex:349`.
- **Variables**: `m` median of `f` (**Q**); `a in R` (**Q**); `t>0`
  (**Q/N**); probability space and measurable `f` inherited (**Hidden/M**).
- **Analytic proof-step checks**: event measurability for absolute-value
  preimages requires `f` measurable; probability bounded by `1` uses
  probability measure; case split on `|m-a|`.
- **Lean counterpart**:
  - `AppendixB.lean`: `half_le_tail_about_center_of_median_far`.
  - `AppendixB.lean`: `median_tail_le_two_tail_about_any_center`.
- **Conclusion/hypotheses match**: Lean statement is explicit about median and
  measurable events.
- **Verdict**: **PASS-exact + TEXT-gap**.  The lemma statement should repeat
  measurability/probability hypotheses or be placed inside a clearly scoped
  paragraph.

### B-08. Lemma: Median Controlled by the Mean

- **Source**: `AppendixB_bookstyle.tex:366`.
- **Variables**: `f >= 0` (**Q/N**); `m` median (**Q**); `E f`
  (**Hidden/I**); probability space/measurable `f` inherited (**Hidden/M**).
- **Analytic proof-step checks**: integral over `{f >= m}` requires
  measurability; finite or extended expectation convention must be fixed.  If
  using real expectation, integrability is required (**I**).
- **Lean counterpart**: used in high-probability good-set/median-to-mean
  bridge; exact theorem family in `AppendixB.lean` and high-probability bridge.
- **Conclusion/hypotheses match**: mathematical result is formalized in the
  relevant concrete contexts, not clearly as this exact standalone lemma.
- **Verdict**: **PASS-conditional + TEXT-gap**.  Add `f` measurable and
  integrable/nonnegative explicitly.

### B-09. Theorem: Spherical Levy Inequality

- **Source**: `AppendixB_bookstyle.tex:387`.
- **Variables**: integer `N` (**Hidden/N**, should be `N>=1` or `N>=2`);
  sphere `S^{N-1}` and surface probability `sigma_{N-1}` (**D**);
  `g:S^{N-1}->R` (**Q**); `L>0` and `L`-Lipschitz (**Q/N**); median `M_g`
  (**Der**, existence asserted); `t>0` (**Q/N**).
- **Analytic proof-step checks**: Lipschitz implies Borel measurable; median
  exists for real measurable functions under probability measure; exponential
  bound is the geometric isoperimetric/Levy input.
- **Lean counterpart**:
  - `AppendixBLevyPolarBridge.lean`: `strongGlobalSurfaceSubtypeLevy`, but it
    takes `hFixedMedianLevy` as an input and packages it into
    `StrongGlobalSurfaceSubtypeLevy`.
  - `AppendixBSphericalConcentration.lean`: consumes
    `GlobalSurfaceSubtypeLevy`/strong variants.
- **Conclusion/hypotheses match**: not no-input at this exact level unless a
  separate fixed-median spherical Levy theorem is present and fed to
  `strongGlobalSurfaceSubtypeLevy`.
- **Verdict**: **PASS-conditional / possible LEAN-gap**.  The book states this
  as a theorem; the Lean artifact I inspected packages the fixed-median Levy
  theorem as an assumption.  Either cite the external geometric theorem as an
  input, or add the no-input Lean theorem proving it from spherical
  isoperimetry.

### B-10. Theorem: Localized Levy Lemma

- **Source**: `AppendixB_bookstyle.tex:402`.
- **Variables**: `Omega_0 subset S^{N-1}` measurable (**Q/M**);
  `sigma(Omega_0) >= 3/4` (**Q/N**); `f:S^{N-1}->R` measurable (**Q/M**);
  `f` `L`-Lipschitz on `Omega_0` (**Q**, should include `L>=0`, and `L>0`
  if used in denominator); median `m_f` (**Q**); `t>0` (**Q/N**).
- **Analytic proof-step checks**: McShane extension requires metric-space
  subset and finite Lipschitz constant; extension is measurable because it is
  Lipschitz; Spherical Levy invoked with Lipschitz constant `L`; center-change
  lemma invoked with measurable `f`; event union bound uses `F=f` on
  `Omega_0`; `Omega_0` positive measure follows from `>=3/4`.
- **Lean counterpart**:
  - `AppendixB.lean`: `localized_levy_lemma_reduction`,
    `localized_levy_lemma`.
- **Conclusion/hypotheses match**: Lean has an abstract localized Levy result
  with explicit measurable set, median, global Levy input, and local Lipschitz
  hypotheses.
- **Verdict**: **PASS-exact + TEXT-gap**.  State `L>0` or handle `L=0`
  separately; repeat all measurability hypotheses locally.

### B-11. Lemma: Layer-Cake Mean Estimate

- **Source**: `AppendixB_bookstyle.tex:448`.
- **Variables**: probability space and measurable `f` (**Hidden/M**);
  center `m` (**Q but not explicitly typed in statement**); radius `R`
  (**Q/N**, should say `R>=0`); `|f-m| <= R` a.s. (**Q/I-deriving**);
  `Phi:[0,R]->[0,infty)` Borel measurable (**Q/M/N**); `int Phi < infinity`
  (**Q/I**); tail bound for `0<=t<=R` (**Q**).
- **Analytic proof-step checks**: layer-cake identity for the nonnegative
  random variable `|f-m|` requires measurability; boundedness gives
  integrability; integral over `[0,R]` requires `R>=0`; comparison uses
  monotonicity of the Lebesgue integral for nonnegative functions.
- **Lean counterpart**:
  - `AppendixB.lean`: `mean_tail_probability_le_median_tail_probability_from_quantitative_bound`.
  - `AppendixB.lean`: `appendixB_mean_concentration_from_integrated_centering`.
- **Conclusion/hypotheses match**: Lean has the integrated-tail machinery, but
  the displayed `Phi` formulation is a book-level restatement.
- **Verdict**: **PASS-stronger + TEXT-gap**.  The patched statement now
  includes `Phi` measurable and finite integral, but still should quantify
  `f`, `m`, `R`, `mu`, and `R>=0` in the lemma itself.

### B-12. Lemma: Telescoping Identity

- **Source**: `AppendixB_bookstyle.tex:480`.
- **Variables**: `A,B in M_D(C)` (**Q**); `k>=1` (**Q/N**).
- **Analytic proof-step checks**: algebra only; matrix multiplication
  associative.
- **Lean counterpart**: deterministic telescoping lemmas in `AppendixB.lean`,
  used by `trace_power_bound_from_telescope_terms`.
- **Conclusion/hypotheses match**: yes.
- **Verdict**: **PASS-exact**.

### B-13. Proposition: Trace-Power Perturbation

- **Source**: `AppendixB_bookstyle.tex:493`.
- **Variables**: `A,B in M_D(C)` (**Q**); `k>=1` (**Q/N**).
- **Analytic proof-step checks**: telescoping identity; trace-norm triangle
  inequality; trace ideal inequality
  `||RST||_1 <= ||R||_op ||S||_1 ||T||_op`; powers controlled by operator
  norm.
- **Lean counterpart**:
  - `AppendixB.lean`: `trace_power_bound_from_telescope_terms`,
    `trace_power_bound_from_telescope_and_hs_op_controls`.
- **Conclusion/hypotheses match**: Lean proves the bound in a finite matrix
  form suited to the partial-transpose moment map.
- **Verdict**: **PASS-stronger**.

### B-14. Proposition: Deterministic Lipschitz Estimate

- **Source**: `AppendixB_bookstyle.tex:529`.
- **Variables**: `X,Y in sphere(X)` (**Q**); `A_X=(XX^*)^Gamma` (**D**);
  `f_k(X)=Tr(A_X^k)` (**D**); `k` (**Hidden/N**, should say `k>=1`);
  `D` (**D**).
- **Analytic proof-step checks**: trace-power perturbation hypotheses with
  `A_X,A_Y`; trace/Frobenius inequality; partial transpose is HS-isometry;
  product-difference identity; HS submultiplicativity
  `||UV||_HS <= ||U||_op ||V||_HS`; triangle inequality.
- **Lean counterpart**:
  - `AppendixB.lean`: `deterministic_lipschitz_from_trace_and_difference_bounds`,
    `deterministic_frobenius_lipschitz_from_operator_and_difference_bounds`,
    `deterministic_frobenius_lipschitz_from_hs_op_telescope_controls`.
- **Conclusion/hypotheses match**: Lean has more parameterized deterministic
  versions; the displayed estimate follows.
- **Verdict**: **PASS-stronger + TEXT-gap**.  Quantify `k>=1` in the
  proposition.

### B-15. Corollary: Lipschitz Scale on the Good Set

- **Source**: `AppendixB_bookstyle.tex:574`.
- **Variables**: `D=d^2` (**Q/D**); `a,b` (**Q/N**, should say positive);
  `d` (**Hidden/N**, should say `d>0`); `k` (**Hidden/N**); `Omega(a,b)`
  (**D**).
- **Analytic proof-step checks**: substitute good-set bounds into deterministic
  Lipschitz estimate; `||X||_op + ||Y||_op <= 2a/d`; maximum partial-transpose
  norm bounded by `b/d^2`; arithmetic of exponents.
- **Lean counterpart**:
  - `AppendixB.lean`: deterministic local Lipschitz assembly and
    `local_lipschitz_concentration_theorem`.
- **Conclusion/hypotheses match**: yes in the local theorem pipeline, but
  constants may be parameterized differently.
- **Verdict**: **PASS-stronger + TEXT-gap**.  Add `a,b>0`, `d>=1`, `k>=1`.

### B-16. Theorem: Complex Wick Formula

- **Source**: `AppendixB_bookstyle.tex:609`.
- **Variables**: finite index set `Xi` (**Hidden/D**); independent standard
  complex Gaussians `z_eta` (**Q/M/I by distribution**); words `h` and
  `bar h` of lengths `r,s` (**Q**).
- **Analytic proof-step checks**: independence; integrability of finite
  products of Gaussian variables; one-coordinate complex Gaussian moments;
  product over coordinates.
- **Lean counterpart**:
  - `ComplexGaussianWick.lean`: balanced and unbalanced complex Wick expansion
    theorems.
- **Conclusion/hypotheses match**: yes for finite words and independent
  standard complex Gaussian coordinates.
- **Verdict**: **PASS-exact + TEXT-gap**.  State `Xi` finite if the proof
  groups over coordinates.

### B-17. Definition: Surviving Wick Permutation

- **Source**: `AppendixB_bookstyle.tex:677`.
- **Variables**: closed walk `i_0,...,i_m=i_0` (**Q**); labels
  `alpha_0,...,alpha_{m-1}` (**Q**); permutation `pi in S_m` (**Q**);
  cyclic edge indexing (**D but should be stated precisely**).
- **Analytic proof-step checks**: none.
- **Lean counterpart**:
  - `AubrunMomentSpine.lean`: `WickPermutationFiber`, `wickLeftSetoid`,
    `wickRightSetoid`, `wickColumnSetoid`.
- **Conclusion/hypotheses match**: yes at the formal relation/fiber level.
- **Verdict**: **PASS-exact**.

### B-18. Proposition: Moment Expansion After Wick's Formula

- **Source**: `AppendixB_bookstyle.tex:698`.
- **Variables**: `m>=1` (**Q/N**); `Z` off-diagonal partial-transpose Wishart
  (**D**); closed walks and sample labels (**Der**).
- **Analytic proof-step checks**: finite trace expansion; finite sums allow
  exchange of expectation and sums; Wick formula applied to products with
  matched holomorphic/conjugate positions; off-diagonal condition measurable
  and deterministic.
- **Lean counterpart**:
  - `AubrunMomentSpine.lean`: surviving-pairing trace-moment expansion.
  - `AppendixBAubrunMomentInput.lean`: `gaussianWishartGammaOffDiagonal_traceMoment_eq_wickSum`,
    `gaussianWishartGammaOffDiagonal_traceMoment_eq_survivingPairing_sum`,
    and norm inequality.
- **Conclusion/hypotheses match**: Lean proves a more explicit finite sum
  identity for the concrete matrix model.
- **Verdict**: **PASS-stronger**.

### B-19. Definition: Profile of a Wick Permutation

- **Source**: `AppendixB_bookstyle.tex:748`.
- **Variables**: permutation `pi` (**Q**); equivalence relations
  `~_L,~_R,~_Sigma` (**D**); class counts `ell_L,ell_R,ell_Sigma` (**D**);
  profile `(u,v)` (**D**).
- **Analytic proof-step checks**: none; counting bound uses class-count
  assignment principle.
- **Lean counterpart**:
  - `AppendixBAubrunGraduate.lean`: `wickRelationProfileCount`.
  - `AubrunMomentSpine.lean`: class-count setoid definitions.
- **Conclusion/hypotheses match**: yes.
- **Verdict**: **PASS-exact**.

### B-20. Lemma: Aubrun Lemma 3.6

- **Source**: `AppendixB_bookstyle.tex:798`.
- **Variables**: innovation pattern (**Q but not formally defined in prose**);
  `U` innovations (**Q/N**); canonical alphabet size at most `k`
  (**Q/N**); compatible tilde-word assignments (**Q but not formally defined).
- **Analytic proof-step checks**: pure finite counting; injection into
  `(Fin U -> Fin k x Fin k x Fin k)`.
- **Lean counterpart**:
  - `AppendixBAubrunGraduate.lean`: `aubrunLemma36_card_le_k_pow_three_mul`
    with hypothesis `encode : Family ↪ (Fin U -> Fin k × Fin k × Fin k)`.
- **Conclusion/hypotheses match**: Lean proves the reusable injection bound.
  The prose proof assumes, but does not define, the encoder from compatible
  tilde assignments to triples of innovation choices.
- **Verdict**: **PASS-conditional + TEXT-gap**.  To be 1-1, the manuscript
  must define the family and the encoding, or state the lemma in the same
  abstract injection form as Lean.

### B-21. Lemma: Fixed-Defect Class Count

- **Source**: `AppendixB_bookstyle.tex:815`.
- **Variables**: defect `Delta` (**Q/N**); `k` (**Q/N**, Lean needs `1<=k`);
  compatible relation classes (**Q but not formally defined); compatibility
  defect (**D? currently informal).
- **Analytic proof-step checks**: finite counting; invokes innovation lift and
  compatibility defect bounds.
- **Lean counterpart**:
  - `AppendixBAubrunGraduate.lean`: `aubrunLemma74_fixedDefectClassCount_le`.
  - `AppendixBAubrunCombinatorics.lean`: `fixedDefectClassCount_le`.
- **Conclusion/hypotheses match**: Lean statement has extra explicit data:
  fibers, left/right couples, an encoding into left/right couples, left/right
  cardinal bounds, and a largeness condition `k <= 2*I.card + 2*Delta` for
  nonempty fibers.
- **Verdict**: **PASS-conditional + TEXT-gap**.  The book statement suppresses
  several hypotheses that Lean requires and that are mathematically meaningful.

### B-22. Theorem: Aubrun Graduate Relation Counting

- **Source**: `AppendixB_bookstyle.tex:831`.
- **Variables**: polynomial `Q` independent of `d,S` (**Der/Q**);
  `m>=1` (**Q/N**); dimensions `d,S` (**Q/N**, should say positive);
  relation counts `N_m(u,v)` (**D**).
- **Analytic proof-step checks**: finite partition by profile/defect;
  summation over finite profile ranges; absorption of defect factors into
  polynomial `Q`; arithmetic with `sqrt S` requires `S>=0`.
- **Lean counterpart**:
  - `AppendixBAubrunGraduate.lean`: `AubrunGraduateRelationCounting` is an
    abbrev/interface.
  - `aubrunGraduateRelationCounting_of_profileCountSumBound`,
    `aubrunGraduateRelationCounting`, and
    `aubrunLemma75_relationCounting_of_profileCountSumBound` all require the
    concrete profile-count inequality `hProfile`.
  - `aubrunProposition73P`, `aubrunProposition71Q` give explicit polynomials
    and polynomial bounds.
- **Conclusion/hypotheses match**: the inspected Lean theorem is conditional
  on `hProfile`; it does not by itself prove the displayed profile-count
  inequality from Lemmas 3.6/7.4.  If a separate no-input canonical profile
  theorem exists, it must be cited here by exact name.
- **Verdict**: **PASS-conditional / likely LEAN-gap**.  The book currently
  presents as no-input what Lean exposes as an interface fed by `hProfile`.

### B-23. Theorem: Off-Diagonal Moment Bound

- **Source**: `AppendixB_bookstyle.tex:863`.
- **Variables**: polynomial `Q` (**Der**); `m>=1` (**Q/N**); `d,S`
  positive (**Hidden/N**); balanced specialization `D=d^2` (**D**);
  `Z` (**D**).
- **Analytic proof-step checks**: Wick expansion; graduate relation-counting
  theorem; normalization factor `S^{-m}` requires `S>0`; finite-sum
  nonnegativity if bounding expectations.
- **Lean counterpart**:
  - `AppendixBAubrunGraduate.lean`: moment/envelope theorems downstream of
    `AubrunGraduateRelationCounting`.
- **Conclusion/hypotheses match**: Lean conclusion matches once
  `AubrunGraduateRelationCounting Q d s m` is supplied.
- **Verdict**: **PASS-conditional**.  This inherits the relation-counting
  conditionality from B-22.

### B-24. Lemma: Even-Moment Extraction

- **Source**: `AppendixB_bookstyle.tex:887`.
- **Variables**: Hermitian random matrix `Z` (**Q**); even `m` (**Q/N**);
  expectation of `Tr(Z^m)` finite and nonnegative (**Hidden/I/N**).
- **Analytic proof-step checks**: pointwise spectral inequality; monotonicity
  of expectation; Jensen/Lyapunov step is actually
  `E||Z|| <= (E||Z||^m)^{1/m}` and then pointwise comparison to trace.  This
  requires integrability and nonnegative random variable.
- **Lean counterpart**: off-diagonal expectation extraction in
  `AppendixBAubrunGraduate.lean`.
- **Conclusion/hypotheses match**: Lean has the moment-to-operator-norm bridge
  in concrete finite-dimensional contexts.
- **Verdict**: **PASS-stronger + TEXT-gap**.  Add finite-moment/integrability
  hypotheses.

### B-25. Theorem: Off-Diagonal Expectation Bound

- **Source**: `AppendixB_bookstyle.tex:901`.
- **Variables**: sequence/regime `S/d^2 -> lambda>0` (**Q/N**);
  constant `C_lambda` (**Der**); `d` sufficiently large (**Der/N**).
- **Analytic proof-step checks**: choice of even `m(d)` with
  `Q(m)=o(d)` and `log d/m -> 0`; moment extraction; asymptotic comparison
  using `S ~ lambda d^2`.
- **Lean counterpart**:
  - `AppendixBAubrunGraduate.lean`:
    `gaussianWishartGammaOffDiagonalOpNormMean_le_expectationEnvelope_of_graduate_relation_counting`.
- **Conclusion/hypotheses match**: Lean has a quantitative envelope theorem
  conditional on graduate relation counting.  The asymptotic `S/d^2 -> lambda`
  statement is a book-level corollary.
- **Verdict**: **PASS-conditional + TEXT-gap**.  The proof needs an explicit
  lemma choosing even `m(d)`.

### B-26. Lemma: Gamma Tail for One Average

- **Source**: `AppendixB_bookstyle.tex:944`.
- **Variables**: `S` positive integer (**Hidden/N**); independent exponential
  variables `E_alpha` mean `1` (**Q**); `xi` defined (**D**); `u>=0`
  (**Q/N**).
- **Analytic proof-step checks**: MGF of Gamma sum; Chernoff bound; optimize
  parameter; independence; measurability/integrability automatic for
  exponentials.
- **Lean counterpart**:
  - `AppendixBDiagonalGamma.lean`: diagonal Gamma tail/maximum expectation
    machinery.
- **Conclusion/hypotheses match**: likely formalized inside the diagonal Gamma
  bridge, but not confirmed as this exact displayed standalone tail theorem.
- **Verdict**: **PASS-conditional**.  Cite exact Lean theorem if the
  standalone tail exists; otherwise mark as proof-internal rather than a named
  formal theorem.

### B-27. Lemma: Maximum of the Diagonal

- **Source**: `AppendixB_bookstyle.tex:963`.
- **Variables**: `u>=0` (**Q/N**); `D,S` positive (**Hidden/N**); diagonal
  variables `W_ii` (**D**); finite index set `I` with `|I|=D` (**D**).
- **Analytic proof-step checks**: one-variable Gamma tail with `u+log D`;
  `D>=1` for `log D`; union bound over finite `I`.
- **Lean counterpart**:
  - `AppendixBDiagonalGamma.lean`: max diagonal expectation/tail machinery,
    e.g. `gaussianDiagonalGammaMaxMean_le_of_sampleDimension_pos`.
- **Conclusion/hypotheses match**: formal bridge is expectation-oriented; the
  exact displayed tail should be cross-cited if present.
- **Verdict**: **PASS-conditional + TEXT-gap**.  Add `D>=1`, `S>=1`; cite the
  exact tail theorem or downgrade to proof sketch.

### B-28. Theorem: Diagonal Expectation Bound

- **Source**: `AppendixB_bookstyle.tex:981`.
- **Variables**: `D=d^2` (**Q/D**); `S/d^2 -> lambda>0` (**Q/N**);
  `C_lambda` (**Der**); large `d` (**Der/N**).
- **Analytic proof-step checks**: integrate maximum tail; deterministic offset
  bounded under balanced scaling; tail integral finite.
- **Lean counterpart**:
  - `AppendixBDiagonalGamma.lean`: `gaussianDiagonalGammaMaxMean_le_C_lambda`,
    `gaussianWishartGammaDiagonalOpNormMean_le_C_lambda`.
- **Conclusion/hypotheses match**: Lean provides the quantitative diagonal
  expectation bound in the finite model.
- **Verdict**: **PASS-stronger**.

### B-29. Theorem: Wishart-Gamma Expectation Bound

- **Source**: `AppendixB_bookstyle.tex:1000`.
- **Variables**: `D=d^2`, `S/d^2 -> lambda>0` (**Q/N**); `W`, `GammaPT`
  (**D**); `C_lambda` (**Der**).
- **Analytic proof-step checks**: diagonal/off-diagonal decomposition;
  triangle inequality for operator norm; diagonal and off-diagonal expectation
  bounds; finite expectations.
- **Lean counterpart**:
  - `AppendixBDiagonalGamma.lean`: `wishartGammaExpectation_from_diagonalGammaMax_and_offDiagonal`
    and related concrete expectation bound.
- **Conclusion/hypotheses match**: yes if off-diagonal bound is supplied.
- **Verdict**: **PASS-conditional** because it inherits B-22/B-23.

### B-30. Lemma: Gaussian Operator Norm

- **Source**: `AppendixB_bookstyle.tex:1029`.
- **Variables**: Gaussian matrix `G in M_{I,Sigma}(C)` (**Q**);
  dimensions `D,S` (**D/N**); universal `C` (**Der**).
- **Analytic proof-step checks**: Gordon/Dudley comparison; centered Gaussian
  process; metric entropy or width bounds; finite dimensions.
- **Lean counterpart**:
  - `AppendixBConcreteBridge.lean`: expectation inputs use existing Gaussian
    operator-norm bounds to prove
    `concreteRemainingExpectationInputs_gaussianExpectation_le_target`.
- **Conclusion/hypotheses match**: downstream Lean proves the normalized target
  bound; the raw Gordon/Dudley lemma may not be exposed with this exact
  statement.
- **Verdict**: **PASS-conditional + possible LEAN-gap**.  The book can keep
  the classical lemma, but the audit needs the exact Lean theorem name for the
  raw unnormalized expectation or should say Lean proves the required
  consequence.

### B-31. Lemma: Radius Estimates

- **Source**: `AppendixB_bookstyle.tex:1053`.
- **Variables**: standard Gaussian `G` (**D**); `R=||G||_HS` (**D**);
  dimensions `D,S` positive (**D/N**); universal `c>0` (**Der/N**).
- **Analytic proof-step checks**: sum of `DS` independent exponentials is
  Gamma `(DS,1)`; expectation formula; lower bound for `E sqrt Z` by Gamma
  ratio or Paley--Zygmund.
- **Lean counterpart**:
  - `AppendixBRadialSpherical.lean`: `gaussianRadiusSq_eq_gaussianMass`.
  - `AppendixBPolarRadial.lean`: radial square integral and lower-bound
    radial mean lemmas.
- **Conclusion/hypotheses match**: yes in the radial package.
- **Verdict**: **PASS-stronger**.

### B-32. Theorem: First Normalized Expectation

- **Source**: `AppendixB_bookstyle.tex:1087`.
- **Variables**: `X` uniform on HS sphere (**D**); `D=d^2` (**Q/D**);
  `S/d^2 -> lambda>0` (**Q/N**); `C_lambda` (**Der**).
- **Analytic proof-step checks**: polar law; independence of `R` and `X`;
  product expectation factorization for nonnegative/integrable
  `R` and `||X||_op`; Gaussian operator-norm bound; radial lower bound;
  asymptotic algebra.
- **Lean counterpart**:
  - `AppendixBConcreteBridge.lean`: `concreteRemainingExpectationInputs_gaussianExpectation_le_target`.
  - `AppendixBRadialSpherical.lean`: `gaussian_sampleOpNorm_expectation_factorization_of_indep`.
  - `AppendixBLevyPolarBridge.lean`: `gaussianRadius_indep_gaussianDirection`.
- **Conclusion/hypotheses match**: Lean proves the concrete target used
  downstream; raw asymptotic phrasing is book-level.
- **Verdict**: **PASS-stronger**, conditional only on B-30 if the raw Gaussian
  bound is not separately exposed.

### B-33. Theorem: Second Normalized Expectation

- **Source**: `AppendixB_bookstyle.tex:1118`.
- **Variables**: `X` uniform on HS sphere (**D**); `D=d^2`, balanced
  `S/d^2 -> lambda>0` (**Q/N**); `C_lambda` (**Der**).
- **Analytic proof-step checks**: radial identity; independence/product
  expectation for `R^2` and spherical operator-norm functional; `E R^2=DS`;
  relation `(GG*)^Gamma = S W^Gamma`; Wishart-gamma expectation bound.
- **Lean counterpart**:
  - `AppendixBConcreteBridge.lean`:
    `concreteRemainingExpectationInputs_wishartGammaExpectation_le_target`.
  - `AppendixBRadialSpherical.lean`:
    `gaussian_quadratic_radial_spherical_factorization_of_indep`.
- **Conclusion/hypotheses match**: Lean proves the exact normalized target
  bound once Wishart-gamma expectation is available.
- **Verdict**: **PASS-conditional**, inheriting off-diagonal/Aubrun status.

### B-34. Theorem: Good Operator-Norm Sets

- **Source**: `AppendixB_bookstyle.tex:1161`.
- **Variables**: `lambda>0` (**Q/N**); constants `a,b,c>0` (**Der/N**);
  large `d` (**Der/N**); `X` sphere variable under `sigma_X` (**D**).
- **Analytic proof-step checks**: first map is globally 1-Lipschitz;
  median controlled by expectation for nonnegative measurable map; spherical
  Levy applied with deviation of order `1/d`; second map local Lipschitz on
  first good set; first good set has mass at least `3/4` for large `d`;
  localized Levy applied; medians of both maps controlled by expectations.
- **Lean counterpart**:
  - `HighProbabilityBounds.lean`: `ConcreteHighProbabilityBoundsExplicit`,
    net/Bernstein tails, `wishart_upper_tail_netLifted`,
    `wishartGamma_upper_tail_netLifted`, `gaussianMass_lower_tail`.
  - `AppendixBConcreteBridge.lean`: `concrete_normalized_operator_norm_probability_inputs`.
- **Conclusion/hypotheses match**: Lean seems to prove the concrete
  high-probability inputs by net/Bernstein rather than by the book's Levy proof
  for both events.  The conclusion is equivalent or stronger for downstream
  purposes.
- **Verdict**: **PASS-stronger + TEXT-gap**.  The proof route in prose should
  match the formal route or explicitly say this is an alternative mathematical
  proof.

### B-35. Theorem: Local Lipschitz Concentration

- **Source**: `AppendixB_bookstyle.tex:1214`.
- **Variables**: fixed `k>=1` (**Q/N**); `lambda>0` (**D/N**);
  constants `c,C>0` (**Der/N**); large `d` (**Der/N**); all `eps>0`
  (**Q/N**); `X` uniform on sphere (**D**); `f_k` (**D/M**).
- **Analytic proof-step checks**: good-set mass; deterministic local Lipschitz
  constant; real dimension `N=2d^2 s_d`; localized Levy; boundedness
  `|f_k|<=1`; layer-cake integration of median-centered tail; two-case
  mean/median replacement; all events measurable.
- **Lean counterpart**:
  - `AppendixB.lean`: `local_lipschitz_concentration_theorem`.
  - `AppendixBFinal.lean`: `final_appendixB_assembly_no_structure_inputs`
    assembles inputs.
- **Conclusion/hypotheses match**: Lean theorem is an abstract assembly from
  explicit inputs and is instantiated downstream by concrete bridges.  The
  book statement is the concrete corollary.
- **Verdict**: **PASS-conditional** unless all concrete input packages are
  named in the theorem citation.  It inherits B-09 and B-22 risks.

### B-36. Theorem: Appendix B Concentration Package

- **Source**: `AppendixB_bookstyle.tex:1342`.
- **Variables**: fixed `k>=1` (**Q/N**); `lambda>0` (**Q/N**);
  sequence `s_d/d^2 -> lambda` (**Q/N**); `X~sigma_X` (**Q/M**);
  `rho=XX^*`, `f_k` (**D**); constants `c,C>0` (**Der/N**); large `d`
  (**Der/N**); all `eps>0` (**Q/N**).
- **Analytic proof-step checks**: direct substitution of local concentration
  theorem; equality `rho^Gamma=(XX*)^Gamma`; no new analytic theorem.
- **Lean counterpart**:
  - `AppendixBFinal.lean`: `final_appendixB_assembly_no_structure_inputs`.
  - `AppendixBPipeline.lean` consumes the final assembly.
- **Conclusion/hypotheses match**: the final Lean assembly is an input-driven
  package theorem; exact no-input status depends on whether `RemainingPolarLevyInputs`,
  `RemainingExpectationInputs`, high-probability inputs, and Aubrun relation
  counting are all instantiated by no-input theorem values.
- **Verdict**: **PASS-conditional**.  The book theorem is mathematically the
  desired final result, but the audit cannot certify it as fully no-input until
  the conditional rows B-09 and B-22 are resolved or explicitly declared as
  imported external theorems.

## Cross-Cutting Hypothesis Checks

1. **Measurability is often inherited by prose context instead of local
   theorem statements.**  This affects B-07, B-08, B-10, B-11, B-24, and
   B-35.  Lean does not allow this ambiguity; the book should include
   measurability in every standalone analytic lemma.

2. **Integrability/finite moments are under-stated.**  B-08, B-11, B-24,
   B-32, and B-33 invoke expectations or product expectation factorization.
   Lean proves these in concrete Gaussian/compact-sphere contexts, but the
   pure-math statements should say either “integrable” or “bounded/finite by
   the preceding lemma.”

3. **Positivity/dimension hypotheses are under-stated.**  B-09 needs `N>=1`
   or `N>=2`; B-10 needs `L>0` if the displayed denominator is used; B-15
   needs `a,b>0,d>=1`; B-26/B-27 need `S>=1,D>=1`; B-34/B-35 need large-`d`
   thresholds before using `Omega_0` mass at least `3/4`.

4. **Proof-route mismatch in high-probability estimates.**  The book proves
   good operator-norm sets by spherical/ localized Levy.  Lean also has a
   substantial net/Bernstein high-probability path.  If the book is meant to
   be a 1-1 translation of Lean, the proof route should be rewritten to match
   the net/Bernstein theorem names and hypotheses.

5. **The two biggest certification risks are geometric Levy and Aubrun
   relation counting.**
   - `strongGlobalSurfaceSubtypeLevy` is a theorem that packages a
     fixed-median Levy hypothesis into the strong API.  The audited file should
     not present spherical Levy as fully formalized unless the no-input
     fixed-median isoperimetric theorem is separately named.
   - `aubrunGraduateRelationCounting` is conditional on `hProfile` in the
     inspected Lean file.  The book's Theorem “Aubrun graduate relation
     counting” suppresses that condition.

## Current Honest Answer to “Is the Mathematical Content Formalized?”

Not as a blanket “yes” for the book-style draft as written.

The downstream Appendix B pipeline is largely mirrored in Lean, and many
book statements are formal consequences of stronger Lean packages.  However,
the book currently presents at least two major interfaces as unconditional
theorems where the inspected Lean files expose conditional packaging:

1. the fixed-median spherical Levy/isoperimetric input behind
   `strongGlobalSurfaceSubtypeLevy`;
2. the profile-count estimate behind `aubrunGraduateRelationCounting`.

Additionally, several reader-facing analytic lemmas need local hypotheses
that Lean enforces but the prose currently leaves to context: measurability,
integrability, positivity, and dimension assumptions.

## Required Fixes Before Calling the Book 1-1 Certified

1. Add local theorem hypotheses in the manuscript for every row marked
   **TEXT-gap**.
2. Decide whether the book follows the Lean proof route or a cleaner
   mathematical proof route.  If it follows Lean, rewrite B-34 to use the
   net/Bernstein high-probability package rather than a Levy proof sketch.
3. For B-09, cite the exact no-input Lean theorem proving fixed-median
   spherical Levy, or label it as an imported geometric theorem.
4. For B-22, cite the exact no-input Lean theorem proving the canonical
   profile-count bound, or state the theorem conditionally with `hProfile`.
5. For every displayed theorem, add a parenthetical Lean anchor with both:
   conclusion matched and hypotheses discharged.

