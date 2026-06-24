# Codex runbook: Appendix C universality proof

Date: 2026-06-23

Purpose: keep Codex oriented while rewriting Appendix C and teaching the proof
back to Kieran.  This is an internal working plan, not article prose.

## Non-negotiable target

Produce a proof skeleton for Appendix C that both authors can reproduce without
hidden computations.

The final mathematical message must be:

```tex
\lambda_m^*(d_1)
  =
  \alpha_m - d_1^{-2} + O(d_1^{-4}).
```

The proof must explain why the first-order root shift is universally `-1`.

## Current source anchor

Working source:

```text
Moment_based_PPT_random_states/with blue edits/main-final.tex
```

Relevant section:

```tex
\section{Universality of the first-order unbalanced correction}
```

Before editing, locate this section again and read it from the moment expansion
through the final divisibility/root-shift conclusion.

## One-line proof map

At a threshold root `\alpha`, the Hankel matrix `H_m(\alpha)` has a
one-dimensional kernel.  The first-order correction is universal because
`H_m^{(1)}-H_m'` vanishes on that kernel after the generating-function identity
turns it into a convolution term killed by the divided-difference lemma.

Formula version:

```tex
f_1(\alpha)=f_0'(\alpha),
\qquad
c(\alpha)=-\frac{f_1(\alpha)}{f_0'(\alpha)}=-1.
```

## Keep-this-fixed dictionary

Do not rename these objects casually during the rewrite.

```tex
M_k(\lambda)       : balanced limiting moments.
M_k^{(1)}(\lambda) : first unbalanced correction.
C(z)              : generating function for M_k.
C^{(1)}(z)        : generating function for M_k^{(1)}.
H_m               : [M_{i+j+1}]_{0\le i,j\le m}.
H_m^{(1)}         : [M_{i+j+1}^{(1)}].
H_m'              : \lambda-derivative of H_m.
H_m^{[2]}         : [(M^2)_{i+j+1}], with (M^2)_k=\sum_{a+b=k}M_aM_b.
f_0               : \det H_m.
f_1               : first correction to \det H_m.
\Sigma_m          : \operatorname{Tr}(\operatorname{adj}(H_m)H_m^{[2]}).
g_m               : threshold factor whose roots are the relevant \alpha_m.
v                 : kernel vector of H_m(\alpha).
```

## Proof DAG

Follow this order.  If one arrow is unclear, stop there and repair it before
moving on.

```text
one-defect NC partitions
  -> generating function C^(1)
  -> coefficient identity
  -> Hankel identity
  -> adjugate trace identity
  -> corank-one reduction
  -> divided-difference cancellation
  -> divisibility f1 = f0' mod g_m
  -> root shift c = -1
```

Expanded as formulas:

```tex
C^{(1)}
  =
  \lambda z^3(C+zC_z)C^2(1+zC)
```

then

```tex
\lambda(M_k^{(1)}-M_k')
  =
  M_k-(M^2)_k,
```

then

```tex
\lambda(H_m^{(1)}-H_m')
  =
  H_m-H_m^{[2]},
```

then

```tex
\lambda(f_1-f_0')
  =
  (m+1)f_0-\Sigma_m.
```

At a root `\alpha` of `g_m`, prove:

```tex
\Sigma_m(\alpha)
  =
  \kappa\,v^T H_m^{[2]}(\alpha)v
  =
  0.
```

Therefore:

```tex
f_1\equiv f_0'\pmod {g_m}.
```

## Main danger list

- Do not present the generating function as magic.  It exists to prove the
  coefficient identity comparing `M_k^{(1)}` with `M_k'`.
- Do not let `f_0'` look like notation noise.  It is forced by root
  perturbation.
- Do not bury the adjugate/kernel step late in the appendix.  This is the heart
  of the proof.
- Do not call the divided-difference lemma a technical trick.  It is the
  cancellation of `v^T H_m^{[2]}v`.
- Do not polish prose before the skeleton is hand-checkable.
- Do not keep Appendix C if the skeleton still feels like a black box after the
  rewrite.

## Two-hour collaboration loop

Use this as the live session script.

### 0. Pre-flight, 5 minutes

- Reopen Appendix C source.
- Identify exactly where the proof of universality starts.
- Write the proof DAG at the top of a scratch note.
- Tell Kieran: "The proof is a kernel cancellation proof; the generating
  function is there only to identify the correction matrix."

### 1. Spine, 15 minutes

Goal: Kieran can say the proof in one paragraph.

Write or explain:

```tex
0=f_0(\alpha+c\varepsilon)+\varepsilon f_1(\alpha)+O(\varepsilon^2)
```

so

```tex
c=-f_1(\alpha)/f_0'(\alpha).
```

Then the entire proof reduces to:

```tex
f_1(\alpha)=f_0'(\alpha).
```

Stop and test Kieran before continuing.

### 2. Generating function block, 30 minutes

Goal: remove the mystery around `C^{(1)}`.

Explain the one-defect partition class:

- exactly one block of size 3 or 4;
- every other block has size 1 or 2.

Derive:

```tex
C^{(1)}
  =
  \lambda z^3(C+zC_z)C^2(1+zC).
```

Required explanation of factors:

- `\lambda`: weight of the defective block;
- `z^3`: smallest defect size;
- `C+zC_z`: pointed/weighted choice;
- `C^2`: ordinary intervals around the defect;
- `1+zC`: optional extra interval producing size 4.

End product:

```tex
\lambda(M_k^{(1)}-M_k')
  =
  M_k-(M^2)_k.
```

Stop and ask Kieran why a generating function appears at all.

Expected answer: it turns the combinatorial correction into derivative minus
convolution.

### 3. Matrix block, 25 minutes

Goal: make the determinant perturbation mechanical.

Translate entrywise:

```tex
\lambda(H_m^{(1)}-H_m')
  =
  H_m-H_m^{[2]}.
```

Then use Jacobi:

```tex
f_0'=\operatorname{Tr}(\operatorname{adj}(H_m)H_m'),
\qquad
f_1=\operatorname{Tr}(\operatorname{adj}(H_m)H_m^{(1)}).
```

Conclude:

```tex
\lambda(f_1-f_0')
  =
  (m+1)f_0-\Sigma_m.
```

Stop and test Kieran: "What is `\Sigma_m`, and why does it appear?"

Expected answer: it is the adjugate trace of the convolution matrix
`H_m^{[2]}` left over after comparing correction and derivative.

### 4. Kernel/adjugate block, 25 minutes

Goal: expose the heart of the proof.

At `g_m(\alpha)=0`, show:

```tex
H_m(\alpha)v=0,
\qquad
\operatorname{adj}(H_m(\alpha))=\kappa vv^T.
```

Then:

```tex
\Sigma_m(\alpha)
  =
  \kappa v^T H_m^{[2]}(\alpha)v.
```

So the only remaining job is:

```tex
v^T H_m^{[2]}(\alpha)v=0.
```

Stop and test Kieran: "Where did the whole universality statement go?"

Expected answer: it became one quadratic form on the null vector.

### 5. Divided-difference block, 25 minutes

Goal: make the cancellation feel inevitable.

Kernel condition:

```tex
\sum_j v_j M_{i+j+1}(\alpha)=0.
```

Needed cancellation:

```tex
\sum_{i,j}v_iv_j
  \sum_{a+b=i+j+1}M_a(\alpha)M_b(\alpha)
  =
  0.
```

Interpretation:

```tex
q(x)=x\sum_i v_i x^i.
```

The null-vector condition says `q` is orthogonal to the relevant low powers.
The convolution quadratic form is the divided-difference expression built from
the same orthogonality, so it vanishes.

Stop and ask Kieran to explain the lemma in words.

Expected answer: the convolution term is killed by the same null-vector
orthogonality, expressed through divided differences.

### 6. Assembly, 20 minutes

Goal: finish the proof without handwaving.

Write:

```tex
\Sigma_m(\alpha)=0
\quad\text{for every root }\alpha\text{ of }g_m.
```

If roots are simple:

```tex
g_m\mid \Sigma_m.
```

Since also `g_m\mid f_0`,

```tex
g_m\mid \lambda(f_1-f_0').
```

Since `g_m(0)\neq 0`,

```tex
g_m\mid f_1-f_0'.
```

Thus:

```tex
f_1(\alpha)=f_0'(\alpha),
\qquad
c=-1.
```

Final test: Kieran explains the sign of `-1`.

## Codex rewrite checklist

Use this checklist during the next editing pass.

- [ ] Add an early "proof idea" paragraph: kernel cancellation, not generating
  function wizardry.
- [ ] Move or duplicate the root-perturbation formula near the beginning.
- [ ] Define `M_k^{(1)}` before introducing `C^{(1)}`.
- [ ] Derive `C^{(1)}` factor by factor.
- [ ] State the coefficient identity as the first key lemma.
- [ ] Translate the coefficient identity into the Hankel matrix identity.
- [ ] State Jacobi's formula and the adjugate trace identities explicitly.
- [ ] Make `\Sigma_m` unavoidable, not mysterious.
- [ ] Prove or cite corank one at roots of `g_m` before using the adjugate rank
  one form.
- [ ] Recast the divided-difference lemma as cancellation of
  `v^T H_m^{[2]}v`.
- [ ] Finish with divisibility, then root perturbation.
- [ ] Add a short "why this proves universality" paragraph.

## Understanding checklist for Kieran

Do not move to prose polish until Kieran can answer these without looking:

- Why is `f_0'` in the proof?
- Why does the generating function appear?
- What is the coefficient identity produced by the generating function?
- What is `H_m^{[2]}`?
- Why does the adjugate become `\kappa vv^T`?
- What exactly is `\Sigma_m(\alpha)`?
- Why does the divided-difference lemma kill `v^T H_m^{[2]}v`?
- Where is the sign `-1` produced?

## Definition of done

Appendix C rewrite is ready for article polishing only when:

- the proof DAG appears explicitly in the text or is obvious from section
  order;
- every displayed identity has a stated role;
- the generating-function block is motivated before it is used;
- the kernel/adjugate reduction is visible as the main proof step;
- Kieran can reproduce the proof from the understanding checklist;
- no part of the proof relies on "this follows by computation" without a
  lemma, reference, or derivation.

## If stuck

Stop at the first unclear arrow in the proof DAG and produce a blocker note in
this format:

```text
Blocked arrow:
Known input:
Desired output:
Missing lemma or explanation:
Can be checked by:
```

Do not continue polishing downstream text while an upstream arrow is unclear.
