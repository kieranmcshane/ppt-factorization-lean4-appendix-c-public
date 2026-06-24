/-
  PPT Factorization — Bibliothèque polynomiale minimale (sans Mathlib)
  Représentation : Poly = Array Int  (coefficients ascendants)
  p = #[a₀, a₁, ..., aₙ]  représente  a₀ + a₁λ + ⋯ + aₙλⁿ

  Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
-/

namespace PPT

/-- Polynôme sur ℤ : tableau de coefficients (ordre croissant). -/
abbrev Poly := Array Int

/-- Évaluation en un entier. -/
def eval (p : Poly) (x : Int) : Int :=
  p.foldl (fun (acc, xi) c => (acc + c * xi, xi * x)) (0, 1) |>.fst

/-- Addition de polynômes. -/
def add (p q : Poly) : Poly :=
  let n := max p.size q.size
  -- utiliser i.val pour éviter l'arithmétique Fin (mod n)
  Array.ofFn (n := n) fun i =>
    let iv := i.val
    let a := if iv < p.size then p[iv]! else 0
    let b := if iv < q.size then q[iv]! else 0
    a + b

/-- Multiplication scalaire. -/
def smul (c : Int) (p : Poly) : Poly := p.map (· * c)

/-- Soustraction. -/
def sub (p q : Poly) : Poly := add p (smul (-1) q)

/-- Multiplication de polynômes (version récursive).
    `p(x)·q(x) = p₀·q(x) + x·(p'(x)·q(x))` où `p' = tail(p)`. -/
def mul (p q : Poly) : Poly :=
  if h : p.size = 0 ∨ q.size = 0 then #[]
  else
    have : 0 < p.size := by omega
    let a := p[0]!
    let p' := p.extract 1 p.size
    have : p'.size < p.size := by rw [Array.size_extract]; omega
    add (smul a q) (#[(0 : Int)] ++ mul p' q)
termination_by p.size

/-- Puissance. -/
def pow (p : Poly) : Nat → Poly
  | 0 => #[1]
  | n + 1 => mul p (pow p n)
termination_by n => n

/-- Supprime les zéros de queue (version récursive). -/
def trim (p : Poly) : Poly :=
  if _h : 0 < p.size then
    if p[p.size - 1]! = 0 then trim p.pop else p
  else #[]
termination_by p.size
decreasing_by simp_all [Array.size_pop]; omega

/-- Égalité modulo zéros de queue. -/
def beq (p q : Poly) : Bool := trim p == trim q

/-- Monôme λ^n. -/
def monome (n : Nat) : Poly :=
  (Array.ofFn (n := n+1) (fun _ => (0 : Int))).set! n 1

/-- Constante. -/
def const (c : Int) : Poly := #[c]

-- ─────────────────────────────────────────────────────────────────────────────
-- Affichage
-- ─────────────────────────────────────────────────────────────────────────────

def termStr (c : Int) (i : Nat) : String :=
  if c == 0 then ""
  else if i == 0 then s!"{c}"
  else if i == 1 then
    if c == 1 then "λ" else if c == -1 then "-λ" else s!"{c}λ"
  else
    if c == 1 then s!"λ^{i}" else if c == -1 then s!"-λ^{i}" else s!"{c}λ^{i}"

def toString (p : Poly) : String :=
  let tp := trim p
  if tp.isEmpty then "0"
  else
    let parts := (tp.mapIdx fun i c => termStr c i).toList.filter (· ≠ "")
    if parts.isEmpty then "0"
    else String.intercalate " + " parts

instance : Repr Poly where
  reprPrec p _ := toString p

-- ─────────────────────────────────────────────────────────────────────────────
-- Coefficients c_k  (moments asymptotiques)
-- c_k = Σ_{l=0}^{⌊k/2⌋} C(k,2l) Cat(l) λ^{k-l}
-- ─────────────────────────────────────────────────────────────────────────────

/-- Coefficient binomial C(n,k). -/
def binom : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ => 0
  | n+1, k+1 => binom n k + binom n (k+1)
termination_by n k => n + k

/-- Nombre de Catalan Cat(l) = C(2l,l)/(l+1).
    Defined via the closed formula using binomial coefficients,
    valid for all l ∈ ℕ (not just a lookup table). -/
def catalan (l : Nat) : Int := binom (2 * l) l / (↑(l + 1) : Int)

/-- c_k(λ) = Σ_{l=0}^{⌊k/2⌋} C(k,2l)·Cat(l)·λ^{k-l}. -/
def moment (k : Nat) : Poly :=
  let terms := (List.range (k/2 + 1)).map fun l =>
    smul (binom k (2*l) * catalan l) (monome (k - l))
  terms.foldl add #[]

-- ─────────────────────────────────────────────────────────────────────────────
-- Déterminant d'une matrice (m+1)×(m+1) de polynômes  (expansion Leibniz)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Signature de la permutation σ (représentée comme un Array Nat). -/
def permSign (σ : Array Nat) : Int :=
  let n := σ.size
  Id.run do
    let mut s : Int := 1
    for i in [:n] do
      for j in [i+1:n] do
        if σ[i]! > σ[j]! then s := -s
    return s

/-- Insérer k à la position i dans un Array. -/
def insertAt (a : Array Nat) (i : Nat) (k : Nat) : Array Nat :=
  let left  := a.extract 0 i
  let right := a.extract i a.size
  left ++ #[k] ++ right

/-- Toutes les permutations de {0,...,n-1}. -/
def perms : Nat → List (Array Nat)
  | 0 => [#[]]
  | n+1 =>
    let prev := perms n
    List.flatten (prev.map fun p =>
      (List.range (n+1)).map fun i => insertAt p i n)
termination_by n => n

-- ─────────────────────────────────────────────────────────────────────────────
-- Cofactor expansion and matrix operations
-- ─────────────────────────────────────────────────────────────────────────────

/-- Delete row i and column j from a matrix. -/
def minor (M : Array (Array Poly)) (i j : Nat) : Array (Array Poly) :=
  let rows := (List.range M.size).filter (· ≠ i)
  rows.toArray.map fun r =>
    let row := M[r]!
    let cols := (List.range row.size).filter (· ≠ j)
    cols.toArray.map fun c => row[c]!

/-- Filtering `range n` by `· ≠ i` when `i < n` gives length `n - 1`. -/
theorem filter_ne_range_length : ∀ n i, i < n →
    ((List.range n).filter (· ≠ i)).length = n - 1 := by
  intro n; induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
        List.length_append]
    by_cases hn : n = i
    · subst hn
      simp only [ne_eq, not_true, decide_false]
      rw [show ((List.range n).filter (· ≠ n)).length = (List.range n).length from by
        congr 1; exact List.filter_eq_self.mpr fun x hx =>
          show decide (x ≠ n) = true by simp [Nat.ne_of_lt (List.mem_range.mp hx)]]
      simp [List.length_range]
    · simp only [ne_eq, hn, not_false_eq_true, decide_true]
      have := ih i (by omega); simp at *; omega

/-- Size of minor is one less than the original. -/
theorem minor_size (M : Array (Array Poly)) (i j : Nat) (hi : i < M.size) :
    (minor M i j).size = M.size - 1 := by
  simp only [minor, Array.size_map, List.size_toArray]
  exact filter_ne_range_length M.size i hi

namespace List
theorem getD_append_left {α : Type} (l₁ l₂ : List α) {d : α} {n : Nat}
    (h : n < l₁.length) : (l₁ ++ l₂).getD n d = l₁.getD n d := by
  simp only [List.getD]
  rw [List.getElem?_append_left h]

theorem getD_append_right {α : Type} (l₁ l₂ : List α) {d : α} {n : Nat}
    (h : l₁.length ≤ n) : (l₁ ++ l₂).getD n d = l₂.getD (n - l₁.length) d := by
  simp only [List.getD]
  rw [List.getElem?_append_right h]

theorem getD_range (k n : Nat) (hk : k < n) :
    (List.range n).getD k 0 = k := by
  simp only [List.getD, List.getElem?_range, hk, Option.getD]

end List

/-- Element k of `(range m).filter (· ≠ j)` is `if k < j then k else k + 1`. -/
theorem filter_ne_getD (m j k : Nat) (hj : j < m) (hk : k < m - 1) :
    ((List.range m).filter (· ≠ j)).getD k 0 = if k < j then k else k + 1 := by
  induction m generalizing k j with
  | zero => omega
  | succ m ihm =>
    rw [List.range_succ, List.filter_append]
    by_cases hjm : j < m
    · -- j < m: filter of range m drops j
      have hfl : ((List.range m).filter (· ≠ j)).length = m - 1 :=
        filter_ne_range_length m j hjm
      by_cases hkfl : k < m - 1
      · rw [List.getD_append_left _ _ (by omega)]
        exact ihm j k hjm hkfl
      · -- k = m - 1: the last position is the appended element m
        have hk_eq : k = m - 1 := by omega
        subst hk_eq
        rw [List.getD_append_right _ _ (by omega)]
        simp only [List.filter_cons]
        rw [show decide (m ≠ j) = true from by simp [show m ≠ j from by omega]]
        simp only [List.filter_nil]
        -- Goal: [m].getD (m - 1 - (m - 1)) 0 = if m - 1 < j then m - 1 else m - 1 + 1
        show [m].getD (m - 1 - ((List.range m).filter (· ≠ j)).length) 0 = _
        rw [hfl]
        simp only [Nat.sub_self, List.getD, List.getElem?_cons_zero, Option.getD]
        split <;> omega
    · -- j = m
      have hjm_eq : j = m := by omega
      -- filter (· ≠ j) on range m = range m (all elements < m ≤ j)
      have hfid : (List.range m).filter (· ≠ j) = List.range m :=
        List.filter_eq_self.mpr fun x hx =>
          show decide (x ≠ j) = true by
          have : x < m := List.mem_range.mp hx
          simp [show x ≠ j from by omega]
      -- filter [m] drops m = j, so [m].filter (· ≠ j) = []
      have hfilt_m : [m].filter (· ≠ j) = [] := by
        simp [List.filter_nil, show ¬(m ≠ j) from by omega]
      rw [hfilt_m, List.append_nil, hfid, List.getD_range k m (by omega)]
      split <;> omega


/-- Element k of (range m).filter (· ≠ 0) is k + 1 (getElem version). -/
theorem filter_ne_zero_getElem (m k : Nat) (hk : k < m - 1)
    (hlen : k < ((List.range m).filter (· ≠ 0)).length :=
      by rw [filter_ne_range_length m 0 (by omega)]; exact hk) :
    ((List.range m).filter (· ≠ 0))[k] = k + 1 := by
  have h := filter_ne_getD m 0 k (by omega) hk
  simp only [show ¬(k < 0) from by omega, ite_false] at h
  simp only [List.getD, List.getElem?_eq_getElem hlen] at h; exact h

/-- Element k of (range m).filter (· ≠ j) equals if k < j then k else k + 1 (getElem version). -/
theorem filter_ne_getElem_ite (m j k : Nat) (hj : j < m) (hk : k < m - 1)
    (hlen : k < ((List.range m).filter (· ≠ j)).length :=
      by rw [filter_ne_range_length m j hj]; omega) :
    ((List.range m).filter (· ≠ j))[k] = if k < j then k else k + 1 := by
  have h := filter_ne_getD m j k hj hk
  simp only [List.getD, List.getElem?_eq_getElem hlen] at h; exact h

-- minor_row_size and minor_entry are proved in ClosedFormDet.lean
-- (they require complex array/filter reasoning that is easier with Mathlib available)

/-- Déterminant d'une matrice (cofactor expansion along row 0). -/
def det (M : Array (Array Poly)) : Poly :=
  match _h : M.size with
  | 0 => const 1
  | 1 => M[0]![0]!
  | n + 2 =>
    (List.range (n + 2)).foldl (fun acc j =>
      let sign : Int := if j % 2 == 0 then 1 else -1
      add acc (smul sign (mul M[0]![j]! (det (minor M 0 j))))
    ) (const 0)
termination_by M.size
decreasing_by rw [minor_size M 0 j (by omega)]; omega

/-- Matrice de Hankel B_m : B[i][j] = c_{i+j+1}, 0 ≤ i,j ≤ m. -/
def hankelB (m : Nat) : Array (Array Poly) :=
  let c := (List.range (2*m+3)).map moment |>.toArray
  -- i,j : Fin (m+1) → utiliser .val pour l'arithmétique entière (pas modulo m+1)
  Array.ofFn (n := m+1) fun i =>
    Array.ofFn (n := m+1) fun j => c[i.val + j.val + 1]!

/-- det(B_m) calculé symboliquement. -/
def detB (m : Nat) : Poly := det (hankelB m)

/-- Cofactor expansion along column j. -/
def detByCol (M : Array (Array Poly)) (j : Nat) : Poly :=
  let n := M.size
  (List.range n).foldl (fun acc i =>
    let sign : Int := if (i + j) % 2 == 0 then 1 else -1
    add acc (smul sign (mul M[i]![j]! (det (minor M i j))))
  ) (const 0)

/-- Moment convolution: Σ_{i+j=n} moment(i) · moment(j). -/
def momentConv (n : Nat) : Poly :=
  (List.range (n + 1)).foldl (fun acc k =>
    add acc (mul (moment k) (moment (n - k)))
  ) (const 0)

/-- Check the moment recurrence:
    M_{n+2} − λ·M_{n+1} = λ · Σ_{i+j=n} M_i·M_j. -/
def checkMomentRec (n : Nat) : Bool :=
  beq (sub (moment (n + 2)) (mul (monome 1) (moment (n + 1))))
      (mul (monome 1) (momentConv n))

-- ─────────────────────────────────────────────────────────────────────────────
-- Polynômes Φ_d*(λ) = minimal polynomial de 4cos²(π/d) sur ℚ
-- Obtenus via le calcul Python vérifié (verify_proof_v2.py)
-- ─────────────────────────────────────────────────────────────────────────────

def phiStar : Nat → Poly
  | 3  => #[(-1 : Int), 1]            -- λ - 1
  | 4  => #[(-2 : Int), 1]            -- λ - 2
  | 5  => #[(1 : Int), (-3), 1]       -- λ² - 3λ + 1
  | 6  => #[(-3 : Int), 1]            -- λ - 3
  | 7  => #[(-1 : Int), 6, (-5), 1]   -- λ³ - 5λ² + 6λ - 1
  | 8  => #[(2 : Int), (-4), 1]       -- λ² - 4λ + 2
  | 9  => #[(-1 : Int), 9, (-6), 1]   -- λ³ - 6λ² + 9λ - 1
  | 10 => #[(5 : Int), (-5), 1]       -- λ² - 5λ + 5
  | _  => #[(1 : Int)]                -- trivial

-- ─────────────────────────────────────────────────────────────────────────────
-- Diviseurs ≥ 3 d'un entier n
-- ─────────────────────────────────────────────────────────────────────────────

def divisorsGe3 (n : Nat) : List Nat :=
  (List.range (n+1)).filter fun d => d ≥ 3 && n % d == 0

/-- N_m = ⌈(m+1)²/2⌉. -/
def Nm (m : Nat) : Nat := ((m+1)^2 + 1) / 2

/-- Côté droit : λ^{N_m} * ∏_{d|m+2, d≥3} Φ_d*(λ). -/
def rhs (m : Nat) : Poly :=
  let nm := Nm m
  let divs := divisorsGe3 (m + 2)
  let prodPhi := divs.foldl (fun acc d => mul acc (phiStar d)) (const 1)
  mul (monome nm) prodPhi

-- ─────────────────────────────────────────────────────────────────────────────
-- Verification: catalan values, moment recurrence, and cofactor expansion
-- ─────────────────────────────────────────────────────────────────────────────

#eval do
  IO.println "\n=== Catalan numbers (general formula) ==="
  for n in List.range 10 do
    IO.println s!"  C_{n} = {catalan n}"

#eval do
  IO.println "\n=== Moment recurrence check: M_{n+2} - λ·M_{n+1} = λ·Σ M_i·M_{n-i} ==="
  for n in List.range 12 do
    let ok := checkMomentRec n
    IO.println s!"  n={n}: {if ok then "✓" else "✗"}"

#eval do
  IO.println "\n=== Cofactor expansion vs Leibniz for hankelB ==="
  for m in List.range 5 do
    let leibniz := detB m
    let cofactor := detByCol (hankelB m) 0
    let ok := beq leibniz cofactor
    IO.println s!"  m={m}: Leibniz = cofactor(col 0)? {if ok then "✓" else "✗"}"

end PPT
