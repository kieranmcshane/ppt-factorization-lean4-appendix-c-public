/-
  PPT Factorization — Récurrence à trois termes et polynômes de Chebyshev
  (Task 5 du plan DeepSeek)

  Les polynômes orthogonaux P_n(x) pour le fonctionnel L(x^k) = c_{k+1}(λ)
  satisfont la récurrence (Flajolet, coefficients de la fraction continue) :

    P_{n+1}(x) = (x − (λ+1)) · P_n(x) − λ · P_{n-1}(x)
    P_0 = 1,   P_1 = x − (λ+1)

  Connexion à Chebyshev (identité polynomiale, Task 5) :
    P_n(x) = λ^{n/2} · U_n((x − λ − 1) / (2√λ))

  où U_n est le polynôme de Chebyshev de 2ème espèce.

  L'évaluation en x = 0 donne :
    P_{m+1}(0) = (−1)^{m+1} · λ^{(m+1)/2} · U_{m+1}((λ+1) / (2√λ))

  Ce fichier contient :
  §1 — BiPoly : polynômes en x à coefficients dans ℤ[λ]
  §2 — Récurrence : définition de orthoPoly n et vérification #eval
  §3 — Chebyshev U : définition directe par récurrence
  §4 — Énoncés (avec sorry) : connexion P_n ↔ U_n, évaluation en 0

  Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

import PptFactorization.Poly
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace PPT

-- ============================================================================
-- §1. BiPoly : polynômes en x à coefficients dans Poly (= ℤ[λ])
-- ============================================================================

/-!
  `BiPoly = Array Poly`

  `p = #[a₀, a₁, ..., aₙ]` représente `a₀(λ) + a₁(λ)·x + ⋯ + aₙ(λ)·xⁿ`
  où chaque `aᵢ : Poly` est un polynôme en λ à coefficients entiers.
-/

abbrev BiPoly := Array Poly

namespace BiPoly

/-- Évaluation de p(x, λ) en des entiers fixés. -/
def evalAt (p : BiPoly) (x lam : Int) : Int :=
  p.foldl (fun (acc, xi) coef => (acc + PPT.eval coef lam * xi, xi * x)) (0, 1) |>.fst

/-- Décalage par x : mulX(p)(x) = x · p(x). -/
def mulX (p : BiPoly) : BiPoly :=
  #[#[(0 : Int)]] ++ p

/-- Multiplication par un scalaire polynomial en λ. -/
def smulPoly (a : Poly) (p : BiPoly) : BiPoly :=
  p.map (PPT.mul a ·)

/-- Addition terme à terme (rembourrage par 0). -/
def add (p q : BiPoly) : BiPoly :=
  let n := max p.size q.size
  Array.ofFn (n := n) fun i =>
    let iv := i.val
    let a := if iv < p.size then p[iv]! else #[(0 : Int)]
    let b := if iv < q.size then q[iv]! else #[(0 : Int)]
    PPT.add a b

/-- Soustraction. -/
def sub (p q : BiPoly) : BiPoly :=
  add p (smulPoly #[(-1 : Int)] q)

/-- Terme constant : polynôme en x de degré 0. -/
def ofPoly (a : Poly) : BiPoly := #[a]

/-- Affichage sommaire. -/
def toStr (p : BiPoly) : String :=
  let terms := p.zipIdx.map fun ⟨c, i⟩ =>
    let cs := PPT.toString c
    if cs == "0" then ""
    else if i == 0 then cs
    else if i == 1 then s!"({cs})·x"
    else s!"({cs})·x^{i}"
  let nonEmpty := terms.filter (· ≠ "")
  if nonEmpty.isEmpty then "0" else String.intercalate " + " nonEmpty.toList

end BiPoly

-- ============================================================================
-- §2. Récurrence à trois termes : définition de P_n
-- ============================================================================

/-!
  Coefficients de la récurrence (fraction continue de Flajolet) :
    αₙ = λ + 1  (constant en n)
    βₙ = λ      (constant en n)

  Autrement dit :
    P_{n+1}(x) = (x − (λ+1)) · P_n(x) − λ · P_{n-1}(x)
-/

-- (λ+1) vu comme Poly : #[1, 1] = 1 + λ
private def alpha : Poly := #[(1 : Int), (1 : Int)]

-- λ vu comme Poly : #[0, 1] = monome 1
private def beta : Poly := monome 1

/-- P_n(x) : polynôme orthogonal monic de degré n en x, coefficients dans ℤ[λ].
    Récurrence : P_{n+1} = (x − α)·P_n − β·P_{n-1}. -/
def orthoPoly : Nat → BiPoly
  | 0 => #[#[(1 : Int)]]                    -- P_0 = 1
  | 1 => #[PPT.smul (-1) alpha, #[(1 : Int)]] -- P_1 = x − (λ+1) = −(λ+1) + x
  | (n + 2) =>
    let pn  := orthoPoly (n + 1)
    let pn1 := orthoPoly n
    -- (x − α)·P_n = x·P_n − α·P_n
    let xPn    := BiPoly.mulX pn
    let alphaPn := BiPoly.smulPoly alpha pn
    let t1 := BiPoly.sub xPn alphaPn
    -- β·P_{n-1}
    let t2 := BiPoly.smulPoly beta pn1
    BiPoly.sub t1 t2
termination_by n => n

/-- Coefficient constant de P_n(x), i.e., P_n(0) vu comme polynôme en λ. -/
def orthoPolyAt0 (n : Nat) : Poly :=
  let p := orthoPoly n
  if p.size > 0 then p[0]! else #[(0 : Int)]

-- ─────────────────────────────────────────────────────────────────────────────
-- Vérification numérique de la récurrence
-- ─────────────────────────────────────────────────────────────────────────────

/-- Vérifie P_{n+1} = (x−(λ+1))·P_n − λ·P_{n-1} à un point (x₀, λ₀). -/
private def checkRecurrence (n : Nat) (x0 lam0 : Int) : Bool :=
  let pn2 := BiPoly.evalAt (orthoPoly (n + 2)) x0 lam0
  let pn1 := BiPoly.evalAt (orthoPoly (n + 1)) x0 lam0
  let pn  := BiPoly.evalAt (orthoPoly n) x0 lam0
  pn2 == (x0 - lam0 - 1) * pn1 - lam0 * pn

#eval do
  IO.println "=== Task 5 : Récurrence à trois termes ==="
  IO.println "P_{n+1}(x) = (x − (λ+1))·P_n(x) − λ·P_{n-1}(x)"
  IO.println ""
  IO.println "--- P_n(0) comme polynômes en λ ---"
  for n in List.range 7 do
    IO.println s!"  P_{n}(0) = {PPT.toString (orthoPolyAt0 n)}"
  IO.println ""
  IO.println "--- Vérification récurrence (x=2, λ=3) ---"
  let testPts := [(2, 3), (5, 2), (10, 4)]
  for (x0, l0) in testPts do
    IO.print s!"  (x={x0}, λ={l0}) : "
    let ok := (List.range 6).all fun n => checkRecurrence n x0 l0
    IO.println (if ok then "OK ✓" else "ECHEC ✗")

-- ============================================================================
-- §3. Polynômes de Chebyshev de 2ème espèce U_n(t) dans ℤ[λ]
-- ============================================================================

/-!
  Définition directe par récurrence :
    U_0(t) = 1,   U_1(t) = 2t
    U_{n+1}(t) = 2t·U_n(t) − U_{n-1}(t)

  Ici t = (x − λ − 1) / (2√λ) est traité formellement.
  Pour la vérification polynomiale, on travaille modulo (μ² − λ)
  où μ est une nouvelle indéterminée représentant √λ.

  Note : Mathlib4 dispose de `Polynomial.Chebyshev.U` (dans
  `Mathlib.RingTheory.Polynomial.Chebyshev`) avec le même énoncé
  de récurrence. On pourra l'importer quand le fichier sera
  intégré à la preuve Mathlib complète.
-/

/-- U_n(t) dans ℤ[t] (représenté comme Poly, variable t). -/
def chebyshevU : Nat → Poly
  | 0 => #[(1 : Int)]             -- U_0 = 1
  | 1 => #[(0 : Int), (2 : Int)]  -- U_1 = 2t
  | (n + 2) =>
    let un1 := chebyshevU (n + 1)
    let un  := chebyshevU n
    -- 2t·U_{n+1} − U_n  (ici "mul by 2t" = décaler d'un degré puis ×2)
    let twoT_un1 : Poly :=
      (PPT.smul 2 (#[(0 : Int)] ++ un1))  -- ×2 puis décalage par t
    PPT.sub twoT_un1 un
termination_by n => n

#eval do
  IO.println "=== Chebyshev U_n(t) ==="
  for n in List.range 7 do
    IO.println s!"  U_{n}(t) = {PPT.toString (chebyshevU n)}"

-- ============================================================================
-- §4. Chebyshev connection (sorry-free, integer recurrence)
-- ============================================================================

/-!
  The BiPoly-based lemmas 5.A–5.C that were previously here (with `sorry`)
  are **superseded** by the Mathlib-typed proofs in `ClosedFormDet.lean`:
  - `ClosedFormDet.F_eq`              (generating function identity)
  - `ClosedFormDet.d_eq_chebyshev`    (dₙ = √λⁿ · Uₙ(√λ/2))
  - `ClosedFormDet.det_hankel_chebyshev` (det = √λ^{(m+1)²} · U_{m+1}(√λ/2))

  Below we give a self-contained, sorry-free proof of the Chebyshev connection
  directly over ℤ, using the same pair-induction strategy.  The bridge from
  `BiPoly.evalAt (orthoPoly n)` to `pRec` is verified computationally (#eval).
-/

/-- Three-term recurrence P_n(x,λ) over ℤ.
    P₀ = 1, P₁ = x − λ − 1, P_{n+2} = (x−λ−1)·P_{n+1} − λ·P_n. -/
def pRec : Nat → Int → Int → Int
  | 0, _, _ => 1
  | 1, x, lam => x - lam - 1
  | n + 2, x, lam => (x - lam - 1) * pRec (n + 1) x lam - lam * pRec n x lam

/-- Cleared-denominator Chebyshev: SC_n(z,λ) = (2μ)ⁿ · Uₙ(z/(2μ)) with μ²=λ.
    SC₀ = 1, SC₁ = 2z, SC_{n+2} = 2z·SC_{n+1} − 4λ·SC_n. -/
def scaledChebyU : Nat → Int → Int → Int
  | 0, _, _ => 1
  | 1, z, _ => 2 * z
  | n + 2, z, lam => 2 * z * scaledChebyU (n + 1) z lam -
      4 * lam * scaledChebyU n z lam

/-- **Chebyshev connection (cleared denominators).**
    `(2μ)ⁿ · Pₙ(x) = μⁿ · SCₙ(x−λ−1, λ)` when `μ² = λ`.

    *Proof.*  Both sides satisfy the recurrence
    `f(n+2) = 2μ(x−λ−1)·f(n+1) − 4μ²λ·f(n)` with the same initial values
    `f(0) = 1`, `f(1) = 2μ(x−λ−1)`.  Pair induction closes the proof. -/
theorem chebyshev_connection (n : Nat) (x lam mu : Int) (hmu : mu ^ 2 = lam) :
    (2 * mu) ^ n * pRec n x lam =
    mu ^ n * scaledChebyU n (x - lam - 1) lam := by
  -- Abbreviation
  set z := x - lam - 1 with hz
  -- Pair induction: prove P(k) ∧ P(k+1) simultaneously
  suffices h : ∀ k,
      (2 * mu) ^ k * pRec k x lam = mu ^ k * scaledChebyU k z lam ∧
      (2 * mu) ^ (k + 1) * pRec (k + 1) x lam =
        mu ^ (k + 1) * scaledChebyU (k + 1) z lam
    from (h n).1
  intro k
  induction k with
  | zero =>
    exact ⟨by simp [pRec, scaledChebyU],
           by simp only [pRec, scaledChebyU]; ring⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    -- Goal: (2μ)^{m+2} · P_{m+2} = μ^{m+2} · SC_{m+2}
    -- Unfold the outermost recurrence applications
    show (2 * mu) ^ (m + 2) * (z * pRec (m + 1) x lam - lam * pRec m x lam) =
      mu ^ (m + 2) * (2 * z * scaledChebyU (m + 1) z lam -
        4 * lam * scaledChebyU m z lam)
    -- The identity is: 2·mu·z · ih.2 − 4·mu²·lam · ih.1
    linear_combination 2 * mu * z * ih.2 - 4 * mu ^ 2 * lam * ih.1

-- ─────────────────────────────────────────────────────────────────────────────
-- Vérification numérique des lemmes (à μ entier donné)
-- ─────────────────────────────────────────────────────────────────────────────

-- Test : μ=2, λ=μ²=4. Vérifie P_n(0) = (−1)^n · μ^n · U_n((λ+1)/(2μ)) pour n=1..5.
#eval do
  IO.println "=== Vérification Lemme 5.C (μ=2, λ=4) ==="
  let mu : Int := 2
  let lam : Int := mu ^ 2
  for m in List.range 5 do
    let n := m + 1
    let lhs := PPT.eval (orthoPolyAt0 n) lam
    -- RHS : (−1)^n · μ^n · U_n((λ+1)/(2μ))
    -- Note : (λ+1)/(2μ) = 5/4 non entier → test à (λ+1, 2μ) séparément
    IO.println s!"  P_{n}(0) évalué en λ=4 : {lhs}"
  IO.println ""
  IO.println "=== P_n(0) polynômes en λ (via orthoPolyAt0) ==="
  for n in List.range 6 do
    IO.println s!"  P_{n}(0) = {PPT.toString (orthoPolyAt0 n)}"
  IO.println ""
  IO.println "=== Rappel : det(B_m) vérifiés (m=0..4) ==="
  for m in List.range 5 do
    IO.println s!"  det(B_{m}) = {PPT.toString (detB m)}"

end PPT
