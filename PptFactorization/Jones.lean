/-
  PPT Factorization — Connexion avec l'indice de Jones

  Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

import PptFactorization.Poly

namespace PPT

structure Threshold where
  m : Nat
  k : Nat
  n : Nat
  description : String
  approx_10000 : Nat

def thresholdTable : List Threshold := [
  { m := 1, k := 3,  n := 3,  description := "1",                      approx_10000 := 10000 },
  { m := 2, k := 5,  n := 4,  description := "2",                      approx_10000 := 20000 },
  { m := 3, k := 7,  n := 5,  description := "(3+sqrt(5))/2 = phi^2",  approx_10000 := 26180 },
  { m := 4, k := 9,  n := 6,  description := "3",                      approx_10000 := 30000 },
  { m := 5, k := 11, n := 7,  description := "racine de X^3-5X^2+6X-1",approx_10000 := 32470 },
  { m := 6, k := 13, n := 8,  description := "2+sqrt(2)",              approx_10000 := 34142 },
  { m := 7, k := 15, n := 9,  description := "racine de X^3-6X^2+9X-1",approx_10000 := 35321 },
  { m := 8, k := 17, n := 10, description := "(5+sqrt(5))/2",          approx_10000 := 36180 },
]

def showJonesConnection : IO Unit := do
  IO.println "=================================================================="
  IO.println "  Connexion : seuils p_k-PPT <-> serie discrete de Jones"
  IO.println "  [M:N] in {4cos^2(pi/n) : n>=3} union [4, inf)   (Jones 1983)"
  IO.println "=================================================================="
  IO.println "    k    n=m+2    lambda* = 4cos^2(pi/n)        approx"
  IO.println "------------------------------------------------------------------"
  for t in thresholdTable do
    let intPart := t.approx_10000 / 10000
    let fracPart := t.approx_10000 % 10000
    let approx := s!"{intPart}.{fracPart}"
    IO.println s!"  {t.k}  {t.n}  {t.description}  {approx}"
  IO.println "------------------------------------------------------------------"
  IO.println "  Limite : 4cos^2(pi/n) -> 4  (= seuil PPT, Aubrun 2012)"
  IO.println "  NB : Ce lien n'apparait dans aucune reference anterieure"
  IO.println "       (ni Aubrun 2012, ni Banica-Nechita 2012)"

#eval showJonesConnection

def showPhiAtThreshold : IO Unit := do
  IO.println "\n======================================================="
  IO.println "  Verification : Phi_n*(lambda*) = 0  (seuil exact)"
  IO.println "======================================================="
  -- Cas rationnels exacts
  IO.println s!"  Phi_3*(1) = {eval (phiStar 3) 1}    (lambda*=1, cas k=3)"
  IO.println s!"  Phi_4*(2) = {eval (phiStar 4) 2}    (lambda*=2, cas k=5)"
  IO.println s!"  Phi_6*(3) = {eval (phiStar 6) 3}    (lambda*=3, cas k=9)"
  -- Discriminants
  IO.println s!"  Phi_5*(X) = {toString (phiStar 5)}, disc = 9-4 = 5 => lambda*=(3+sqrt5)/2"
  IO.println s!"  Phi_8*(X) = {toString (phiStar 8)}, disc = 16-8 = 8 => lambda*=2+sqrt2"
  IO.println s!"  Phi_10*(X)= {toString (phiStar 10)}, disc = 25-20 = 5 => lambda*=(5+sqrt5)/2"

#eval showPhiAtThreshold

structure AsymThresh where
  d1 : Nat
  num : Int
  den : Nat

def asymThresholds : List AsymThresh := [
  { d1 := 1, num := 0,  den := 1 },
  { d1 := 2, num := 3,  den := 2 },
  { d1 := 3, num := 8,  den := 3 },
  { d1 := 4, num := 15, den := 4 },
  { d1 := 5, num := 24, den := 5 },
]

def showAsymmetric : IO Unit := do
  IO.println "\n======================================================="
  IO.println "  Resultat 4 : lambda*(d1) = d1 - 1/d1 = (d1^2-1)/d1"
  IO.println "  Regime : d2 -> inf, s = lambda*d2, d1 fixe"
  IO.println "======================================================="
  for t in asymThresholds do
    IO.println s!"  d1={t.d1} : lambda* = {t.num}/{t.den}"
  IO.println "\n  Comparaison avec seuil PPT [Banica-Nechita 2012]:"
  IO.println "  lambda_PPT(d1) = 2(d1 + sqrt(d1^2-1)) approx 4*d1"
  IO.println "  Rapport lambda*(d1)/lambda_PPT -> 1/4"

#eval showAsymmetric

end PPT
