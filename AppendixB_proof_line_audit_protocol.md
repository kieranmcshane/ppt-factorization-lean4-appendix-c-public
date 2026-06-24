# Appendix B Proof-Line Audit Protocol

This supersedes the weaker theorem-level audit standard for the expository
Appendix B drafts.

The theorem-level audit asks whether a displayed statement has a Lean
counterpart.  That is not enough.  A manuscript can have a formally correct
destination while hiding nontrivial steps inside the prose proof.  The new
standard audits every displayed proof transition.

## Required Unit of Audit

Every displayed proof chain is decomposed into line-to-line transitions.

For a chain

```tex
\[
\begin{aligned}
L_0
&\le L_1\\
&= L_2\\
&\le L_3,
\end{aligned}
\]
```

the audit contains separate rows for:

1. `L_0 -> L_1`,
2. `L_1 -> L_2`,
3. `L_2 -> L_3`.

The same applies to prose transitions containing words such as “therefore,”
“hence,” “by,” “since,” “it follows,” “using,” “after integration,” “by
independence,” “by Levy,” or “by Wick.”

## Mandatory Row Schema

Each proof-line row must contain:

| Field | Meaning |
|---|---|
| Source | File, theorem/lemma/proposition, proof paragraph, displayed line. |
| Transition | The exact mathematical move from previous expression/event to next. |
| Variables used | Every variable used in the transition, classified as defined, quantified, measurable, integrable, nonnegative/positive, or derived. |
| Justification class | Algebra, definition, local lemma, analytic theorem, finite-dimensional norm theorem, probability theorem, asymptotic estimate, external citation, or Lean theorem. |
| Hypotheses required | The exact hypotheses of the invoked theorem or inequality. |
| Hypotheses discharged? | Where each hypothesis was proved/stated. |
| Lean counterpart | Exact Lean theorem if this line is meant to correspond to a formal step; otherwise “pure prose standard theorem” with citation/proof. |
| Manuscript action | None, add proof, add citation, add hypothesis, split into lemma, or mark external input. |
| Status | PASS, PASS-after-edit, TEXT-gap, LEAN-gap, or EXTERNAL-input. |

## Forbidden Justifications

The following are not acceptable as proof-line justifications:

- “standard” without either a proof, a citation, or a named theorem;
- “obvious” for any inequality involving norms, expectations, integrals,
  medians, measure pushforwards, measurability, independence, asymptotics, or
  cardinality estimates;
- “by Lean” without matching both the conclusion and the hypotheses of the
  actual Lean theorem;
- “by concentration” without naming the concentration theorem and checking its
  Lipschitz, measurability, median, positivity, and dimension hypotheses.

## Proof-Line Classification Tags

- **ALG**: algebraic expansion, cancellation, associativity, distributivity,
  cyclicity of trace.
- **DEF**: unfolding a definition.
- **LOC**: previously proved local lemma in the manuscript.
- **LEAN**: exact Lean theorem; conclusion and hypotheses both match.
- **NORM**: nontrivial finite-dimensional norm inequality.
- **MEAS**: measurability or event measurability.
- **INT**: integrability, finite expectation, Tonelli/Fubini, layer cake.
- **PROB**: probability inequality, union bound, median property, independence.
- **CONC**: concentration theorem such as Levy, Bernstein, Gamma Chernoff.
- **ASYM**: asymptotic comparison or choice of a sequence.
- **COUNT**: finite combinatorial counting/injection/cardinality step.
- **EXT**: external theorem not formalized in Lean.

## Red-Flag Moves Requiring Automatic Expansion

The following moves must be expanded in the manuscript unless they were already
proved as a local lemma:

1. `|Tr M| <= ||M||_1`.
2. `||RST||_1 <= ||R||_op ||S||_1 ||T||_op`.
3. `||UV||_HS <= ||U||_op ||V||_HS`.
4. Any use of trace cyclicity.
5. Any exchange of expectation with a sum, integral, supremum, or limit.
6. Any layer-cake identity.
7. Any use of independence to factor an expectation.
8. Any assertion that a pushforward measure is a probability measure.
9. Any assertion that a function is measurable because it is Lipschitz or
   continuous on a subtype.
10. Any median existence or median center replacement step.
11. Any application of Levy/Bernstein/Gamma concentration.
12. Any union bound over a family whose cardinality is not displayed.
13. Any asymptotic choice such as “choose \(m(d)\) slowly enough.”
14. Any combinatorial estimate that hides an injection, quotient, fiber count,
    or profile regrouping.

## Acceptance Gate

A theorem proof passes the proof-line audit only if every displayed transition
has one of these outcomes:

1. **PASS**: all hypotheses are locally visible and the step is justified.
2. **PASS-after-edit**: the manuscript was edited so the missing justification
   is now visible.
3. **EXT**: the step is explicitly marked as an external theorem with a
   precise citation.

Any **TEXT-gap** or **LEAN-gap** blocks the claim “1-1 certified.”

## Pilot Audit: Trace-Power Perturbation

This is the example that exposed the weakness of the previous audit.

Statement:

\[
  |\Tr(A^k)-\Tr(B^k)|
  \le
  k\max(\|A\|_{\op},\|B\|_{\op})^{k-1}\|A-B\|_1.
\]

Variables:

- `A,B in M_D(C)`: quantified.
- `k >= 1`: quantified, positive.
- trace norm/operator norm: defined earlier.
- finite dimension: defined by matrix algebra.

### PL-TP-01. Telescoping expansion

- **Transition**:
  \[
    A^k-B^k=\sum_{j=0}^{k-1}A^j(A-B)B^{k-1-j}.
  \]
- **Class**: ALG/LOC.
- **Hypotheses required**: associative multiplication; `k>=1`.
- **Discharged**: lemma “Telescoping identity.”
- **Lean counterpart**: deterministic telescoping lemmas in `AppendixB.lean`.
- **Status**: PASS.

### PL-TP-02. Trace linearity and scalar triangle inequality

- **Transition**:
  \[
  |\Tr(A^k)-\Tr(B^k)|
  =
  \left|\sum_j \Tr(M_j)\right|
  \le
  \sum_j |\Tr(M_j)|.
  \]
- **Class**: ALG/NORM.
- **Hypotheses required**: finite sum; linearity of trace; triangle inequality
  in `C`.
- **Discharged**: finite matrix context.
- **Manuscript action**: added explicitly.
- **Status**: PASS-after-edit.

### PL-TP-03. Trace bounded by trace norm

- **Transition**:
  \[
    |\Tr(M_j)|\le \|M_j\|_1.
  \]
- **Class**: NORM.
- **Hypotheses required**: finite-dimensional trace norm; identity has
  operator norm `1`; trace/operator norm duality.
- **Discharged**: proof now refers to trace-norm/operator-norm duality.
- **Manuscript action**: added explicitly.
- **Status**: PASS-after-edit.

### PL-TP-04. Schatten ideal inequality

- **Transition**:
  \[
    \|A^j(A-B)B^{k-1-j}\|_1
    \le
    \|A^j\|_{\op}\|A-B\|_1\|B^{k-1-j}\|_{\op}.
  \]
- **Class**: NORM.
- **Hypotheses required**: matrices composable; finite-dimensional Schatten
  ideal property.
- **Discharged**: proof inserted using trace-norm/operator-norm duality and
  trace cyclicity.
- **Manuscript action**: added explicitly.
- **Status**: PASS-after-edit.

### PL-TP-05. Operator norm powers

- **Transition**:
  \[
    \|A^j\|_{\op}\le \|A\|_{\op}^j,\qquad
    \|B^{k-1-j}\|_{\op}\le \|B\|_{\op}^{k-1-j}.
  \]
- **Class**: NORM.
- **Hypotheses required**: submultiplicativity of operator norm.
- **Discharged**: stated explicitly in proof.
- **Status**: PASS-after-edit.

### PL-TP-06. Maximum bound and summation

- **Transition**:
  \[
    \sum_{j=0}^{k-1}
    \|A\|_{\op}^j\|A-B\|_1\|B\|_{\op}^{k-1-j}
    \le
    k\max(\|A\|_{\op},\|B\|_{\op})^{k-1}\|A-B\|_1.
  \]
- **Class**: ALG/NORM.
- **Hypotheses required**: operator norms and trace norm nonnegative;
  finite sum has `k` terms; `k>=1`.
- **Discharged**: nonnegativity of norms; statement has `k>=1`.
- **Status**: PASS.

## Pilot Audit: Mean Deviation From Median Deviation

Statement:

\[
  |\mathbb E f-m|\le a,\quad u>a
  \implies
  \{|f-\mathbb E f|\ge u\}\subset \{|f-m|\ge u-a\}.
\]

Variables:

- `f`: measurable and integrable if `E f` is a real number.
- `m,a,u`: quantified real numbers.
- `a`: should be nonnegative or at least derived from `|\mathbb E f-m|<=a`,
  which implies `a>=0`.
- `u>a`: quantified positivity relative to `a`.

### PL-MD-01. Pointwise triangle inequality

- **Transition**:
  \[
    |f(x)-m|
    =
    |(f(x)-\mathbb E f)+(\mathbb E f-m)|
    \ge
    |f(x)-\mathbb E f|-|\mathbb E f-m|.
  \]
- **Class**: ALG/NORM.
- **Hypotheses required**: `E f` exists as a real number.
- **Discharged**: should be stated by integrability of `f`; currently often
  inherited from context.
- **Status**: PASS-after-edit for proof expansion; TEXT-gap if the enclosing
  lemma does not state integrability.

### PL-MD-02. Event inclusion

- **Transition**: from pointwise implication for arbitrary `x` to event
  inclusion.
- **Class**: PROB/SET.
- **Hypotheses required**: none beyond well-defined events.
- **Discharged**: measurability required only for taking probabilities later.
- **Status**: PASS.

### PL-MD-03. Taking probabilities

- **Transition**:
  \[
    E_1\subset E_2\implies \mathbb P(E_1)\le\mathbb P(E_2).
  \]
- **Class**: PROB/MEAS.
- **Hypotheses required**: `E_1,E_2` measurable.
- **Discharged**: requires `f` measurable.
- **Status**: PASS-after-edit for proof text; TEXT-gap if measurability is not
  stated in the lemma scope.

## Full-Manuscript Audit Procedure

1. Split each proof into proof-line transitions.
2. Fill the mandatory row schema for each transition.
3. Patch the manuscript immediately for every hidden standard theorem.
4. Re-run compilation.
5. Only then update theorem-level audit status.

The old theorem-level audit remains useful as an index, but it is no longer a
certification standard.

