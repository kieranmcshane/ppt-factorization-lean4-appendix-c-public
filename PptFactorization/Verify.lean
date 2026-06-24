/-
  PPT Factorization — Vérification formelle en Lean 4

  Finite determinant factorization checks:
    det(B_m) = λ^{N_m} * ∏_{d|m+2, d≥3} Φ_d*(λ)

  Formal status:
  - m=0,1,2 : compiled Lean theorems using `native_decide`;
  - m=0..8  : runtime `#eval` diagnostics using the safe finite `Φ_d*` table;
  - general m: not formalized in this file.

  Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

import PptFactorization.Poly

namespace PPT

-- ─────────────────────────────────────────────────────────────────────────────
-- Vérification computationnelle complète (m=0..8)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Runtime diagnostic for `m=0..8`.

This is useful evidence, but not a theorem certificate.  It uses
`verifyDetFactorization?`, so unsupported cyclotomic factors are reported as
unsupported instead of silently omitted. -/
def verifyAll : IO Unit := do
  IO.println "================================================================="
  IO.println "  Runtime check: det(B_m) = lambda^{N_m} * prod Phi_d*(lambda)"
  IO.println "================================================================="
  let mut allOk := true
  for m in List.range 9 do
    let dB := detB m
    let nm := Nm m
    let divs := divisorsGe3 (m+2)
    match rhs? m with
    | some r =>
      let ok := beq dB r
      if !ok then allOk := false
      let status := if ok then "✓" else "✗"
      IO.println s!"  m={m} k={2*m+1} N_m={nm} divs={divs}  {status}  det={toString dB}"
    | none =>
      allOk := false
      IO.println s!"  m={m} k={2*m+1} N_m={nm} divs={divs}  unsupported Phi* factor"
  IO.println "================================================================="
  IO.println (if allOk then
    "  Runtime checks passed for m = 0..8 (not theorem-level certification)"
  else
    "  Runtime check failed or hit an unsupported Phi* factor")

-- The diagnostic is intentionally not executed during normal builds/CI.
-- To run it interactively, temporarily evaluate:
--
--   #eval verifyAll

-- ─────────────────────────────────────────────────────────────────────────────
-- Théorèmes formels certifiés (native_decide)
-- Pour m≥3 le calcul O((m+1)!) est trop lourd pour native_decide dans la VM.
-- L'utilisateur peut les vérifier localement sur une machine plus puissante.
-- ─────────────────────────────────────────────────────────────────────────────

/-- m=0 theorem-certified check using the safe finite `Φ_d*` API. -/
theorem factorization_m0 : verifyDetFactorization? 0 = some true := by native_decide

/-- m=1, k=3 theorem-certified check using the safe finite `Φ_d*` API. -/
theorem factorization_m1 : verifyDetFactorization? 1 = some true := by native_decide

/-- m=2, k=5 theorem-certified check using the safe finite `Φ_d*` API. -/
theorem factorization_m2 : verifyDetFactorization? 2 = some true := by native_decide

-- ─────────────────────────────────────────────────────────────────────────────
-- Examples for m=3..8.
--
-- These are not part of the compiled formal artifact.  They are local
-- experiments one may try on a faster machine; the repository only counts the
-- theorem statements above as Lean-certified determinant factorization cases.
-- ─────────────────────────────────────────────────────────────────────────────

/-
  Sur machine locale (pas de contrainte de temps) :

  theorem factorization_m3 : verifyDetFactorization? 3 = some true := by native_decide
  -- m=3, k=7 : λ⁸(λ²-3λ+1), seuil λ*=(3+√5)/2=φ²

  theorem factorization_m4 : verifyDetFactorization? 4 = some true := by native_decide
  -- m=4, k=9 : λ¹³(λ-3)(λ-1), seuil λ*=3

  theorem factorization_m5 : verifyDetFactorization? 5 = some true := by native_decide
  -- m=5, k=11 : λ¹⁸(λ³-5λ²+6λ-1), seuil λ*≈3.247

  theorem factorization_m6 : verifyDetFactorization? 6 = some true := by native_decide
  -- m=6, k=13 : λ²⁵(λ-2)(λ²-4λ+2), seuil λ*=2+√2

  theorem factorization_m7 : verifyDetFactorization? 7 = some true := by native_decide
  -- m=7, k=15 : λ³²(λ-1)(λ³-6λ²+9λ-1), seuil λ*≈3.532

  theorem factorization_m8 : verifyDetFactorization? 8 = some true := by native_decide
  -- m=8, k=17 : λ⁴¹(λ²-3λ+1)(λ²-5λ+5), seuil λ*=(5+√5)/2
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- Corollaire : connexion avec l'indice de Jones
-- ─────────────────────────────────────────────────────────────────────────────

/-
  Corollaire (voir Jones.lean) :
  λ*(p_{2m+1}-PPT) = max racine de Φ_{m+2}*(λ) = 4cos²(π/(m+2))
  ∈ {4cos²(π/n) : n≥3}  (série discrète de Jones 1983)

  Cela fait de chaque critère p_k-PPT un "détecteur de subfacteur"
  de profondeur m = (k-1)/2.
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- Plan de preuve générale (analytique)
-- ─────────────────────────────────────────────────────────────────────────────

/-
  Schéma de la preuve (étapes à formaliser avec Mathlib) :

  1. J-fraction pour c_k :
       ∑_k c_k t^k = CF(α=λ, β=λ)  (Prop 4.1 + asymptotique d→∞)

  2. Formule de Heine :
       det(B_m) = λ^{(m+1)²/2} · P_{m+1}(0) / leading_coeff
     où P_n sont les polynômes orthogonaux associés à la J-fraction.

  3. Récurrence de Chebyshev :
       P_n = (x-λ)P_{n-1} - λP_{n-2}
     ⟹ P_n(0) = (-λ)^{n/2} U_n(√λ/2)  (polynômes de Chebyshev U_n)

  4. Factorisation cyclotomique :
       U_{m+1}(√λ/2) = ∏_{d|m+2, d≥3} Φ_d*(λ)
     analogue de  x^n - 1 = ∏_{d|n} Φ_d^{cyc}(x)

  5. Conclusion :
       det(B_m) = λ^{N_m} · ∏_{d|m+2, d≥3} Φ_d*(λ)    □
-/

end PPT
