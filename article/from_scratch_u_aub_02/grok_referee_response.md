# Response to Grok Referee Report

This file records how the final Grok referee objections were handled in the
current `main.tex`.

## Required Edits

1. **One-sided envelope comparison.** Fixed.  The proof now uses the correct
   sufficient inequality
   \[
     \mathcal Q_m^2=(4(m+1))^{72}\ge (2(m+1))^3,
   \]
   hence \((2(m+1))^{3g}\le \mathcal Q_m^{2g}\).

2. **Origin of the analytic cutoffs.** Fixed.  The text now states that the
   offsets \(m+3\) and \(m+1\) come from the separated Wick base exponents
   before defects are charged, and that the reduction applies only where the
   resulting powers are nonnegative.

3. **Binomial padding.** Fixed.  The bidefect envelope definition now explains
   that \(\binom{m+1}{b}\mathcal Q_m^b\) is deliberate padding introduced to
   split the scalar sum into two shifted binomial bases.

4. **Loss parameter.** Fixed.  The definition of \(\mathcal Q_m\) now says that
   the exponent \(36\) is imported from the ambient compatible-couple estimates;
   the reduction itself only needs a sufficiently large loss and allows any
   larger \(Q\).

5. **Out-of-range defect pairs.** Fixed.  A remark after the main theorem now
   says the theorem makes no assertion for \(a>m+3\) or \(b>m+1\).

6. **Cayley graph convention.** Fixed.  The introduction now states that all
   Cayley lengths are taken in the Cayley graph of \(\mathfrak S_n\) generated
   by transpositions.

7. **Second scalar base.** Fixed.  The scalar absorption section now states
   that \(S\) is an abstract second base, instantiated by the \(\sqrt{s}\)-scale
   in the balanced Wishart application.

8. **Conditional scope in the title.** Fixed.  The title now begins
   “A Conditional Bidefect Reduction,” so the result is not advertised as an
   unconditional Aubrun moment theorem.

9. **Concrete sanity check.** Fixed.  Section 2 now includes a small
   \(S_3\)-table illustrating the rank/bidefect identity.

## Current Verdict

The article remains a conditional reduction note.  It is not an unconditional
proof of the full random-matrix theorem, and it does not claim that U-AUB-02 is
closed.
