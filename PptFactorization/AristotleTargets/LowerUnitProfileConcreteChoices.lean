import PptFactorization.AppendixBLowerBoundClosure

/-!
Aristotle handoff for the lower-bound closure.

Target: close the canonical spike-profile supplier used as `hUnitProfile` in
`AppendixB.lower_eventual_log_over_spikeSpeed_concreteModel_of_concreteScalarChoices`.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.

Allowed inputs/context: use existing local lemmas from
`PptFactorization.AppendixBLowerBoundClosure` and its imports, plus mathlib.
Do not add axioms, `opaque`, `unsafe`, new theorem parameters, or weaken the
statement.

Known relevant definitions/lemmas:
* `AppendixB.lowerConcreteCanonicalDirection`
* `AppendixB.lowerConcreteDirectionCapSet`
* `AppendixB.lowerConcreteProfileError`
* `AppendixB.columnDirectionSpikeProfile`
* `AppendixB.betaColumnIntervalSet`
* `AppendixB.betaColumnSpikeScale`
* `AppendixB.lowerConcreteDelta`
* `AppendixB.lowerConcreteN`
* `AppendixB.spikeSpeed`
* `AppendixB.rankOneProjectorGamma`
* `AppendixB.pureSpikeContribution`
* `AppendixB.coordinateUnitVector`

PROVIDED SOLUTION:
Prove the statement below directly.  The intended estimate is that, on the
Beta interval around
`q = betaColumnSpikeScale (lowerConcreteN d) (spikeSpeed k d) a` and on the
projective cap of radius `1 / lowerConcreteNcap d` around the canonical
coordinate vector, the pure spike contribution is eventually at least `a^k`
up to the concrete profile error `lowerConcreteDelta a slack d`.  Preserve the
theorem statement exactly.
-/
namespace AppendixB

open PptFactorization.RandomMatrixModel
open Filter
open scoped Topology Kronecker ComplexOrder

/-!
The canonical coordinate direction itself is algebraically harmless: its
rank-one projector is fixed by partial transpose.  The remaining profile debt
is therefore not at the exact centre, but in propagating this lower trace-power
bound across the projective cap.
-/
theorem lower_rankOneProjectorGamma_coordinateUnitVector_eq
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (i₀ : BipIndex p q) :
    PptFactorization.HighProbabilityBounds.rankOneProjectorGamma (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀) =
      PptFactorization.HighProbabilityBounds.rankOneProjector (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀) := by
  ext i j
  rcases i₀ with ⟨a, b⟩
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  by_cases hi1 : i₁ = a <;> by_cases hi2 : i₂ = b <;>
    by_cases hj1 : j₁ = a <;> by_cases hj2 : j₂ = b <;>
      simp [PptFactorization.HighProbabilityBounds.rankOneProjectorGamma,
        PptFactorization.HighProbabilityBounds.rankOneProjector,
        PptFactorization.RandomMatrixModel.gamma,
        Matrix.partialTranspose, coordinateUnitVector, hi1, hi2, hj1, hj2]

theorem lower_rankOneProjector_coordinateUnitVector_sq_eq
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (i₀ : BipIndex p q) :
    (PptFactorization.HighProbabilityBounds.rankOneProjector (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀)) ^ 2 =
      PptFactorization.HighProbabilityBounds.rankOneProjector (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀) := by
  ext i j
  rcases i₀ with ⟨a, b⟩
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  by_cases hi1 : i₁ = a <;> by_cases hi2 : i₂ = b <;>
    by_cases hj1 : j₁ = a <;> by_cases hj2 : j₂ = b <;>
      simp [pow_two, Matrix.mul_apply,
        PptFactorization.HighProbabilityBounds.rankOneProjector,
        coordinateUnitVector, hi1, hi2, hj1, hj2]

theorem lower_rankOneProjector_coordinateUnitVector_pow_eq
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (i₀ : BipIndex p q) {k : ℕ} (hk : 0 < k) :
    (PptFactorization.HighProbabilityBounds.rankOneProjector (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀)) ^ k =
      PptFactorization.HighProbabilityBounds.rankOneProjector (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀) := by
  let P :=
    PptFactorization.HighProbabilityBounds.rankOneProjector (p := p) (q := q)
      (coordinateUnitVector (ι := BipIndex p q) i₀)
  have hP2 : P ^ 2 = P := by
    simpa [P] using
      lower_rankOneProjector_coordinateUnitVector_sq_eq
        (p := p) (q := q) i₀
  induction k with
  | zero => cases hk
  | succ n ih =>
      cases n with
      | zero => simp
      | succ n =>
          have ih' : P ^ Nat.succ n = P := ih (Nat.succ_pos n)
          rw [pow_succ, ih']
          simpa [pow_two] using hP2

theorem lower_rankOneProjectorGamma_coordinateUnitVector_pow_trace_re
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (i₀ : BipIndex p q) {k : ℕ} (hk : 0 < k) :
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := p) (q := q)
        (coordinateUnitVector (ι := BipIndex p q) i₀)) ^ k).trace.re = 1 := by
  rw [lower_rankOneProjectorGamma_coordinateUnitVector_eq
    (p := p) (q := q) i₀]
  rw [lower_rankOneProjector_coordinateUnitVector_pow_eq
    (p := p) (q := q) i₀ hk]
  have hnorm : ‖coordinateUnitVector (ι := BipIndex p q) i₀‖ = 1 :=
    norm_coordinateUnitVector (ι := BipIndex p q) i₀
  have htrace :=
    PptFactorization.HighProbabilityBounds.rankOneProjector_trace_eq_inner
      (p := p) (q := q)
      (u := coordinateUnitVector (ι := BipIndex p q) i₀)
  rw [htrace]
  rw [inner_self_eq_norm_sq_to_K]
  simp [hnorm]

theorem lower_columnDirectionSpikeProfile_coordinateUnitVector_eq
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (i₀ : BipIndex p q) {N R : ℝ} {k : ℕ} (hk : 0 < k) :
    columnDirectionSpikeProfile (p := p) (q := q) N k R
        (coordinateUnitVector (ι := BipIndex p q) i₀) =
      N ^ (k - 1) * R ^ k := by
  unfold columnDirectionSpikeProfile pureSpikeContribution
  rw [lower_rankOneProjectorGamma_coordinateUnitVector_pow_trace_re
    (p := p) (q := q) i₀ hk]
  ring

theorem lower_spikeSpeed_pow_eq_lowerConcreteN_pow_succ
    {k d : ℕ} (hk : 0 < k) (hd : 0 < d) :
    spikeSpeed k d ^ k = (lowerConcreteN d : ℝ) ^ (k + 1) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  unfold spikeSpeed lowerConcreteN
  rw [Nat.cast_pow]
  rw [← Real.rpow_natCast ((d : ℝ) ^ (2 + (2 : ℝ) / (k : ℝ))) k]
  rw [← Real.rpow_mul (le_of_lt hdR)]
  have hright :
      ((d : ℝ) ^ 2) ^ (k + 1) =
        (d : ℝ) ^ ((2 : ℝ) * (k + 1 : ℕ)) := by
    rw [← Real.rpow_natCast ((d : ℝ) ^ 2) (k + 1)]
    have h2 : ((d : ℝ) ^ 2) = (d : ℝ) ^ (2 : ℝ) :=
      (Real.rpow_natCast (d : ℝ) 2).symm
    rw [h2]
    rw [← Real.rpow_mul (le_of_lt hdR)]
  rw [hright]
  congr 1
  field_simp [hkR]
  norm_num

theorem lowerConcreteN_mul_betaColumnSpikeScale_pow_eq
    {k d : ℕ} (hk : 0 < k) (hd : 0 < d) (a : ℝ) :
    (lowerConcreteN d : ℝ) ^ (k - 1) *
        (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a) ^ k =
      a ^ k := by
  have hN_ne : (lowerConcreteN d : ℝ) ≠ 0 := by
    unfold lowerConcreteN
    positivity
  have hSpeed :=
    lower_spikeSpeed_pow_eq_lowerConcreteN_pow_succ
      (k := k) (d := d) hk hd
  simpa [betaColumnSpikeScale, sharpSphericalRadiusSq] using
    pureQuadratic_sharp_radius_scale_eq_of_speed_pow
      (N := (lowerConcreteN d : ℝ)) (speed := spikeSpeed k d)
      (a := a) (k := k) (Nat.succ_le_of_lt hk) hN_ne hSpeed

theorem lower_columnDirectionSpikeProfile_coordinateUnitVector_betaScale_eq
    {k d : ℕ} (hk : 0 < k) (hd : 0 < d) (a : ℝ) :
    columnDirectionSpikeProfile (p := Fin d) (q := Fin d)
        (lowerConcreteN d) k
        (betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
        (coordinateUnitVector
          (ι := BipIndex (Fin d) (Fin d))
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))) =
      a ^ k := by
  rw [lower_columnDirectionSpikeProfile_coordinateUnitVector_eq
    (p := Fin d) (q := Fin d)
    (((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d)) :
      BipIndex (Fin d) (Fin d))
    (N := lowerConcreteN d)
    (R := betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
    (k := k) hk]
  exact
    lowerConcreteN_mul_betaColumnSpikeScale_pow_eq
      (k := k) (d := d) hk hd a

theorem lower_columnDirectionSpikeProfile_coordinateUnitVector_of_massLower
    {k : ℕ} {ε a slack Rmass : ℝ} {d : ℕ}
    (hk : 0 < k) (hd : 0 < d) (ha_nonneg : 0 ≤ a)
    (hMassLower :
      betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a ≤ Rmass) :
    a ^ k - lowerConcreteProfileError k ε a slack d ≤
      columnDirectionSpikeProfile
        (p := Fin d) (q := Fin d)
        (lowerConcreteN d) k Rmass
        (coordinateUnitVector
          (ι := BipIndex (Fin d) (Fin d))
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))) := by
  let q0 := betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a
  have hprofile_R :
      columnDirectionSpikeProfile
        (p := Fin d) (q := Fin d)
        (lowerConcreteN d) k Rmass
        (coordinateUnitVector
          (ι := BipIndex (Fin d) (Fin d))
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))) =
        (lowerConcreteN d : ℝ) ^ (k - 1) * Rmass ^ k := by
    exact
      lower_columnDirectionSpikeProfile_coordinateUnitVector_eq
        (p := Fin d) (q := Fin d)
        (((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d)) :
          BipIndex (Fin d) (Fin d))
        (N := lowerConcreteN d) (R := Rmass) (k := k) hk
  have hscale :
      (lowerConcreteN d : ℝ) ^ (k - 1) * q0 ^ k = a ^ k := by
    simpa [q0] using
      lowerConcreteN_mul_betaColumnSpikeScale_pow_eq
        (k := k) (d := d) hk hd a
  have hq_nonneg : 0 ≤ q0 := by
    have hspeed_nonneg : 0 ≤ spikeSpeed k d := by
      have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
      exact le_of_lt (by simp [spikeSpeed, Real.rpow_pos_of_pos hdR])
    dsimp [q0, betaColumnSpikeScale]
    exact div_nonneg (mul_nonneg ha_nonneg hspeed_nonneg) (sq_nonneg _)
  have hpow_le : q0 ^ k ≤ Rmass ^ k :=
    pow_le_pow_left₀ hq_nonneg hMassLower k
  have hNpow_nonneg : 0 ≤ (lowerConcreteN d : ℝ) ^ (k - 1) := by
    positivity
  have ha_le :
      a ^ k ≤ (lowerConcreteN d : ℝ) ^ (k - 1) * Rmass ^ k := by
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hpow_le hNpow_nonneg
  have herr_nonneg : 0 ≤ lowerConcreteProfileError k ε a slack d := by
    simp [lowerConcreteProfileError, lowerConcreteDelta]
  rw [hprofile_R]
  linarith

/-- Inner product with a coordinate unit vector reads off that coordinate. -/
theorem lower_inner_coordinateUnitVector_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (u : EuclideanSpace ℂ ι) :
    inner ℂ (coordinateUnitVector (ι := ι) i) u = u i := by
  unfold coordinateUnitVector
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hnot
    simp at hnot

/-- The projective coordinate overlap is exactly the squared norm of the
corresponding coordinate. -/
theorem lower_coordinateUnitVector_overlap_sq_eq_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (u : EuclideanSpace ℂ ι) :
    ‖inner ℂ (coordinateUnitVector (ι := ι) i) u‖ ^ 2 = ‖u i‖ ^ 2 := by
  rw [lower_inner_coordinateUnitVector_eq]

theorem lower_betaColumnIntervalSet_left_le {q δ R : ℝ} :
    R ∈ betaColumnIntervalSet q δ → q ≤ R := by
  intro h
  exact h.1

theorem lower_canonicalDirection_cap_inner_sq_ge
    (a slack : ℝ) {d : ℕ} (hd : 0 < d)
    {u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))}
    (hCap :
      u ∈
        lowerConcreteDirectionCapSet
          lowerConcreteCanonicalDirection a slack d) :
    1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2 ≤
      ‖inner ℂ
        (coordinateUnitVector
          (ι := BipIndex (Fin d) (Fin d))
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d)))
        u‖ ^ 2 := by
  simpa [lowerConcreteDirectionCapSet, lowerConcreteCanonicalDirection, hd,
    ambientProjectiveCapSet] using hCap

/-- Exact remaining cap-stability input for the canonical unit-profile block.

The Beta mass/scaling bookkeeping is closed below.  What remains genuinely
geometric/algebraic is this trace-power estimate for the partially transposed
rank-one projector throughout the projective cap around the coordinate product
vector. -/
def lowerConcreteCanonicalCapSpikeTraceStability
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
          u ∈
            lowerConcreteDirectionCapSet
              lowerConcreteCanonicalDirection a slack d →
          ‖u‖ = 1 →
            let q0 : ℝ :=
              betaColumnSpikeScale
                (lowerConcreteN d : ℝ) (spikeSpeed k d) a
            let T : ℝ :=
              ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
                  (p := Fin d) (q := Fin d) u) ^ k).trace.re
            0 ≤ T ∧
              a ^ k - lowerConcreteProfileError k ε a slack d ≤
                (lowerConcreteN d : ℝ) ^ (k - 1) * (q0 ^ k * T)

/-- Pure scalar cap-loss budget for the canonical unit-profile block.

For each fixed spike height `a`, the projective cap radius `1 / d^2` should
make the trace loss small enough to be absorbed by the concrete profile error.
This isolates the asymptotic scalar part from the geometric trace-power
estimate below. -/
def lowerConcreteCanonicalCapProfileScalarBudget
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a : ℝ, spikeRoot k ε < a →
    ∀ slack : ℝ, 0 < slack →
      ∀ᶠ d in atTop,
        a ^ k - lowerConcreteProfileError k ε a slack d ≤
          a ^ k *
            (1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2) ^ k

/-- Geometric trace-power lower bound on the canonical projective cap.

This is the remaining local algebra/geometry statement after removing the
scalar `a^k` budget.  It compares the real trace power of the partially
transposed rank-one projector to the cap overlap with the canonical coordinate
product vector. -/
def lowerConcreteCanonicalCapTracePowerOverlapLower
    (k : ℕ) : Prop :=
  ∀ a slack : ℝ,
    ∀ᶠ d in atTop,
      ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
        u ∈
          lowerConcreteDirectionCapSet
            lowerConcreteCanonicalDirection a slack d →
        ‖u‖ = 1 →
          let T : ℝ :=
            ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
                (p := Fin d) (q := Fin d) u) ^ k).trace.re
          0 ≤ T ∧
            (1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2) ^ k ≤ T

/-- Coordinate-overlap dominance for the partially transposed rank-one
projector trace power.

This is the true remaining unit-profile algebraic statement: for a unit vector
`u`, the `k`th trace power of the partial transpose of `|u><u|` dominates the
`2k`th power of its overlap with the canonical product coordinate. -/
def lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap
    (k : ℕ) : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d,
    ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
      ‖u‖ = 1 →
        let i₀ : BipIndex (Fin d) (Fin d) :=
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
        let T : ℝ :=
          ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
              (p := Fin d) (q := Fin d) u) ^ k).trace.re
        0 ≤ T ∧
          ‖inner ℂ
            (coordinateUnitVector (ι := BipIndex (Fin d) (Fin d)) i₀)
            u‖ ^ (2 * k) ≤ T

/-- Left reduced density of a bipartite vector, written as the row Gram
matrix.  This is the finite-dimensional object whose trace powers give the
Schmidt-side formula for powers of the partially-transposed rank-one
projector. -/
noncomputable def lowerLeftReducedDensity
    {p q : Type*} [Fintype q]
    (u : EuclideanSpace ℂ (BipIndex p q)) : Matrix p p ℂ :=
  fun a c => ∑ b : q, u (a, b) * star (u (c, b))

/-- Coefficient matrix of a bipartite vector in the product basis. -/
noncomputable def lowerCoeffMatrix
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => u (a, b)

/-- The left reduced density is exactly `A Aᴴ` for the coefficient matrix
`A` of the bipartite vector. -/
theorem lowerLeftReducedDensity_eq_coeff_mul_conjTranspose
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :
    lowerLeftReducedDensity u =
      lowerCoeffMatrix u * Matrix.conjTranspose (lowerCoeffMatrix u) := by
  ext a c
  simp [lowerLeftReducedDensity, lowerCoeffMatrix, Matrix.mul_apply]

/-- Tensor swap operator on `Fin d × Fin d`, written as a matrix. -/
def lowerTensorSwap (d : ℕ) :
    Matrix (BipIndex (Fin d) (Fin d)) (BipIndex (Fin d) (Fin d)) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

/-- Right multiplication by `lowerTensorSwap` swaps the column tensor indices. -/
theorem lower_mul_tensorSwap_apply
    (d : ℕ)
    (M : Matrix (BipIndex (Fin d) (Fin d)) (BipIndex (Fin d) (Fin d)) ℂ)
    (i j : BipIndex (Fin d) (Fin d)) :
    (M * lowerTensorSwap d) i j = M i (j.2, j.1) := by
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (jb, ja)]
  · simp [lowerTensorSwap]
  · intro x _ hx
    have hne : x ≠ (jb, ja) := hx
    have hnot : ¬(x.1 = jb ∧ x.2 = ja) := by
      intro h
      rcases h with ⟨h1, h2⟩
      exact hne (Prod.ext h1 h2)
    simp [lowerTensorSwap, hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ (jb, ja))).elim

/-- Left multiplication by `lowerTensorSwap` swaps the row tensor indices. -/
theorem lower_tensorSwap_mul_apply
    (d : ℕ)
    (M : Matrix (BipIndex (Fin d) (Fin d)) (BipIndex (Fin d) (Fin d)) ℂ)
    (i j : BipIndex (Fin d) (Fin d)) :
    (lowerTensorSwap d * M) i j = M (i.2, i.1) j := by
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (ib, ia)]
  · simp [lowerTensorSwap]
  · intro x _ hx
    have hne : x ≠ (ib, ia) := hx
    have hnot : ¬(ia = x.2 ∧ ib = x.1) := by
      intro h
      rcases h with ⟨h1, h2⟩
      exact hne (Prod.ext h2.symm h1.symm)
    simp [lowerTensorSwap, hnot]
  · intro hnot
    exact (hnot (Finset.mem_univ (ib, ia))).elim

/-- The tensor swap matrix is an involution. -/
theorem lower_tensorSwap_mul_self
    (d : ℕ) :
    lowerTensorSwap d * lowerTensorSwap d =
      (1 : Matrix (BipIndex (Fin d) (Fin d)) (BipIndex (Fin d) (Fin d)) ℂ) := by
  ext i j
  rw [lower_tensorSwap_mul_apply, lowerTensorSwap]
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  by_cases h1 : ib = jb
  · by_cases h2 : ia = ja
    · subst h1; subst h2; simp
    · simp [h1, h2]
  · simp [h1]

/-- Trace identity for the swap operator:
`trace ((B ⊗ₖ C) * S) = trace (B * C)` where `S` swaps tensor coordinates. -/
theorem lower_trace_kronecker_mul_tensorSwap
    (d : ℕ) (B C : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (((B ⊗ₖ C) * lowerTensorSwap d)) = Matrix.trace (B * C) := by
  classical
  calc
    Matrix.trace (((B ⊗ₖ C) * lowerTensorSwap d))
        = ∑ i : BipIndex (Fin d) (Fin d), (((B ⊗ₖ C) * lowerTensorSwap d) i i) := by
            simp [Matrix.trace]
    _ = ∑ i : BipIndex (Fin d) (Fin d), (B ⊗ₖ C) i (i.2, i.1) := by
            simp [lower_mul_tensorSwap_apply]
    _ = ∑ i : BipIndex (Fin d) (Fin d), B i.1 i.2 * C i.2 i.1 := by
            simp
    _ = Matrix.trace (B * C) := by
            symm
            simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
            simpa using
              (Fintype.sum_prod_type'
                (f := fun x y : Fin d => B x y * C y x)).symm

/-- Swap/kronecker commutation for square tensor factors. -/
theorem lower_tensorSwap_mul_kronecker
    (d : ℕ)
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    lowerTensorSwap d * (A ⊗ₖ B) = (B ⊗ₖ A) * lowerTensorSwap d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  simp [lower_tensorSwap_mul_apply, lower_mul_tensorSwap_apply, mul_comm]

/-- Rank-one partial transpose factorization:
`H_u = (A ⊗ Aᴴ) S` with `A` the coefficient matrix of `u`. -/
theorem lower_rankOneProjectorGamma_eq_kronecker_coeff_conjTranspose_mul_tensorSwap
    (d : ℕ)
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :
    PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u =
      ((lowerCoeffMatrix u) ⊗ₖ Matrix.conjTranspose (lowerCoeffMatrix u)) *
        lowerTensorSwap d := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨c, e⟩
  simp [lower_mul_tensorSwap_apply, lowerCoeffMatrix]

/-- Squared rank-one partial transpose in kronecker form:
`H_u^2 = (AAᴴ) ⊗ (AᴴA)`. -/
theorem lower_rankOneProjectorGamma_sq_eq_kronecker_leftRight
    (d : ℕ)
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :
    (PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ 2 =
      ((lowerCoeffMatrix u * Matrix.conjTranspose (lowerCoeffMatrix u)) ⊗ₖ
        (Matrix.conjTranspose (lowerCoeffMatrix u) * lowerCoeffMatrix u)) := by
  let A : Matrix (Fin d) (Fin d) ℂ := lowerCoeffMatrix u
  calc
    (PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ 2
        = (((A ⊗ₖ Matrix.conjTranspose A) * lowerTensorSwap d) *
            ((A ⊗ₖ Matrix.conjTranspose A) * lowerTensorSwap d)) := by
          simp [lower_rankOneProjectorGamma_eq_kronecker_coeff_conjTranspose_mul_tensorSwap, A,
            pow_two]
    _ = (A ⊗ₖ Matrix.conjTranspose A) *
          (lowerTensorSwap d * (A ⊗ₖ Matrix.conjTranspose A)) *
            lowerTensorSwap d := by
          simp [mul_assoc]
    _ = (A ⊗ₖ Matrix.conjTranspose A) *
          ((Matrix.conjTranspose A ⊗ₖ A) * lowerTensorSwap d) *
            lowerTensorSwap d := by
          simp [lower_tensorSwap_mul_kronecker]
    _ = ((A ⊗ₖ Matrix.conjTranspose A) * (Matrix.conjTranspose A ⊗ₖ A)) *
          (lowerTensorSwap d * lowerTensorSwap d) := by
          simp [mul_assoc]
    _ = ((A ⊗ₖ Matrix.conjTranspose A) * (Matrix.conjTranspose A ⊗ₖ A)) * 1 := by
          simp [lower_tensorSwap_mul_self]
    _ = (A * Matrix.conjTranspose A) ⊗ₖ (Matrix.conjTranspose A * A) := by
          simpa [mul_assoc] using
            (Matrix.mul_kronecker_mul A (Matrix.conjTranspose A)
              (Matrix.conjTranspose A) A).symm

/-- Powers distribute over the kronecker product for square matrices. -/
theorem lower_kronecker_pow
    {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    (A ⊗ₖ B) ^ n = (A ^ n) ⊗ₖ (B ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, pow_zero]
      symm
      exact Matrix.kroneckerMap_one_one (fun x y : ℂ => x * y)
        (by simp) (by simp) (by simp)
  | succ n ih =>
      rw [pow_succ, ih, pow_succ, pow_succ]
      simpa using
        (Matrix.mul_kronecker_mul (A ^ n) A (B ^ n) B).symm

/-- Even powers of the rank-one partial transpose from the squared kronecker
factorization. -/
theorem lower_rankOneProjectorGamma_even_power_eq_kronecker_leftRight
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) (p : ℕ) :
    (PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ (2 * p) =
      (((lowerCoeffMatrix u * Matrix.conjTranspose (lowerCoeffMatrix u)) ^ p) ⊗ₖ
        ((Matrix.conjTranspose (lowerCoeffMatrix u) * lowerCoeffMatrix u) ^ p)) := by
  rw [pow_mul]
  rw [lower_rankOneProjectorGamma_sq_eq_kronecker_leftRight]
  rw [lower_kronecker_pow]

/-- Moving one coefficient matrix through powers of the right Gram matrix. -/
theorem lower_coeff_mul_conjTranspose_power_succ
    {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    (A * Matrix.conjTranspose A) ^ (n + 1) =
      A * ((Matrix.conjTranspose A * A) ^ n) * Matrix.conjTranspose A := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      rw [ih]
      rw [pow_succ]
      simp [mul_assoc]

/-- The left and right Gram matrices have the same trace powers. -/
theorem lower_trace_left_right_power_eq
    {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    Matrix.trace ((A * Matrix.conjTranspose A) ^ n) =
      Matrix.trace ((Matrix.conjTranspose A * A) ^ n) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [lower_coeff_mul_conjTranspose_power_succ]
      rw [Matrix.trace_mul_cycle]
      rw [← pow_succ']

/-- Odd trace powers of the rank-one partial transpose match the corresponding
trace powers of the left reduced density. -/
theorem lower_rankOneProjectorGamma_odd_trace_eq_leftReducedDensity_trace
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) (p : ℕ) :
    Matrix.trace
        ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
            (p := Fin d) (q := Fin d) u) ^ (2 * p + 1)) =
      Matrix.trace (((lowerLeftReducedDensity u) ^ (2 * p + 1))) := by
  let A : Matrix (Fin d) (Fin d) ℂ := lowerCoeffMatrix u
  let ρ : Matrix (Fin d) (Fin d) ℂ := A * Matrix.conjTranspose A
  let σ : Matrix (Fin d) (Fin d) ℂ := Matrix.conjTranspose A * A
  have hleft : lowerLeftReducedDensity u = ρ := by
    simp [ρ, A, lowerLeftReducedDensity_eq_coeff_mul_conjTranspose]
  calc
    Matrix.trace
        ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
            (p := Fin d) (q := Fin d) u) ^ (2 * p + 1))
        =
          Matrix.trace
            ((((ρ ^ p) * A) ⊗ₖ ((σ ^ p) * Matrix.conjTranspose A)) *
              lowerTensorSwap d) := by
            rw [pow_succ]
            rw [lower_rankOneProjectorGamma_even_power_eq_kronecker_leftRight]
            rw [lower_rankOneProjectorGamma_eq_kronecker_coeff_conjTranspose_mul_tensorSwap]
            simp [A, ρ, σ, mul_assoc, Matrix.mul_kronecker_mul]
    _ = Matrix.trace (((ρ ^ p) * A) * ((σ ^ p) * Matrix.conjTranspose A)) := by
            rw [lower_trace_kronecker_mul_tensorSwap]
    _ = Matrix.trace ((ρ ^ p) * (A * (σ ^ p) * Matrix.conjTranspose A)) := by
            simp [mul_assoc]
    _ = Matrix.trace ((ρ ^ p) * (ρ ^ (p + 1))) := by
            rw [lower_coeff_mul_conjTranspose_power_succ]
    _ = Matrix.trace (ρ ^ (2 * p + 1)) := by
            congr 1
            rw [← pow_add]
            congr 1
            omega
    _ = Matrix.trace ((lowerLeftReducedDensity u) ^ (2 * p + 1)) := by
            rw [hleft]

/-- The left reduced density `ρ = A Aᴴ` is positive semidefinite. -/
theorem lowerLeftReducedDensity_posSemidef
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) :
    (lowerLeftReducedDensity u).PosSemidef := by
  rw [lowerLeftReducedDensity_eq_coeff_mul_conjTranspose]
  simpa using
    (Matrix.posSemidef_self_mul_conjTranspose (A := lowerCoeffMatrix u))

/-- Every natural power of the left reduced density is positive semidefinite. -/
theorem lowerLeftReducedDensity_pow_posSemidef
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) (k : ℕ) :
    ((lowerLeftReducedDensity u) ^ k).PosSemidef :=
  (lowerLeftReducedDensity_posSemidef (d := d) u).pow k

/-- The real trace of any natural power of the left reduced density is
nonnegative. -/
theorem lowerLeftReducedDensity_trace_pow_re_nonneg
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) (k : ℕ) :
    0 ≤ (Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re := by
  have hpsd :
      ((lowerLeftReducedDensity u) ^ k).PosSemidef :=
    lowerLeftReducedDensity_pow_posSemidef (d := d) u k
  exact (Complex.nonneg_iff.mp hpsd.trace_nonneg).1

/-- The real diagonal of the left reduced density is the squared row norm. -/
theorem lowerLeftReducedDensity_diag_re
    {p q : Type*} [Fintype q]
    (u : EuclideanSpace ℂ (BipIndex p q)) (a : p) :
    ((lowerLeftReducedDensity u) a a).re =
      ∑ b : q, ‖u (a, b)‖ ^ 2 := by
  simp [lowerLeftReducedDensity, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]

/-- A coordinate overlap is bounded by the corresponding diagonal entry of the
left reduced density. -/
theorem lower_coordinate_overlap_sq_le_leftReducedDensity_diag_re
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (u : EuclideanSpace ℂ (BipIndex p q)) (i : BipIndex p q) :
    ‖inner ℂ (coordinateUnitVector (ι := BipIndex p q) i) u‖ ^ 2 ≤
      ((lowerLeftReducedDensity u) i.1 i.1).re := by
  rw [lower_coordinateUnitVector_overlap_sq_eq_norm_sq]
  rw [lowerLeftReducedDensity_diag_re]
  exact Finset.single_le_sum (s := Finset.univ) (a := i.2)
    (f := fun b : q => ‖u (i.1, b)‖ ^ 2)
    (fun b _ => sq_nonneg _) (Finset.mem_univ i.2)

/-- Power version of the coordinate-overlap/left-density diagonal comparison. -/
theorem lower_coordinate_overlap_pow_le_leftReducedDensity_diag_re_pow
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (u : EuclideanSpace ℂ (BipIndex p q)) (i : BipIndex p q) (k : ℕ) :
    ‖inner ℂ (coordinateUnitVector (ι := BipIndex p q) i) u‖ ^ (2 * k) ≤
      ((lowerLeftReducedDensity u) i.1 i.1).re ^ k := by
  have hsq :=
    lower_coordinate_overlap_sq_le_leftReducedDensity_diag_re
      (p := p) (q := q) u i
  have hnonneg :
      0 ≤ ‖inner ℂ (coordinateUnitVector (ι := BipIndex p q) i) u‖ ^ 2 := by
    positivity
  have hpow := pow_le_pow_left₀ hnonneg hsq k
  simpa [pow_mul] using hpow

/-- Sharper trace-power frontier behind `hTraceDominance`.

This asks for the spectral/Schmidt trace-power fact in the precise form needed
after the coordinate-overlap bookkeeping has been closed: the trace power of
the partially-transposed rank-one projector dominates the `k`th power of the
corresponding diagonal entry of the left reduced density. -/
def lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower
    (k : ℕ) : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d,
    ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
      ‖u‖ = 1 →
        let i₀ : BipIndex (Fin d) (Fin d) :=
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
        let T : ℝ :=
          ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
              (p := Fin d) (q := Fin d) u) ^ k).trace.re
        0 ≤ T ∧
          ((lowerLeftReducedDensity u) i₀.1 i₀.1).re ^ k ≤ T

/-- First split component of the left-density trace-power frontier:
the distinguished diagonal entry of the left reduced density, raised to `k`, is
bounded by the real trace power of that reduced density. -/
def lowerLeftReducedDensityDiagonalPowerLeTracePower
    (k : ℕ) : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d,
    ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
      ‖u‖ = 1 →
        let i₀ : BipIndex (Fin d) (Fin d) :=
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
        (((lowerLeftReducedDensity u) i₀.1 i₀.1).re) ^ k ≤
          ((Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re)

/-- Matrix-only core behind `lowerLeftReducedDensityDiagonalPowerLeTracePower`.

This isolates the spectral inequality from the bipartite-vector packaging:
for positive semidefinite matrices, the distinguished diagonal entry (real
part) raised to `k` is bounded by the real trace of the `k`th power. -/
def lowerPosSemidefDiagonalPowerLeTracePowerCore
    (k : ℕ) : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d,
    ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
      ρ.PosSemidef →
        let i₀ : Fin d := ⟨0, hd⟩
        ((ρ i₀ i₀).re) ^ k ≤ ((Matrix.trace (ρ ^ k)).re)

/-- A coordinate quadratic form is the real diagonal entry. -/
theorem lower_quadraticForm_coordinateUnitVector_eq_diag_re
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i : n) :
    HighDimensionalProbability.quadraticForm A
      (coordinateUnitVector (ι := n) i) = (A i i).re := by
  unfold HighDimensionalProbability.quadraticForm coordinateUnitVector
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toEuclideanCLM]
  rw [Matrix.mulVec_single_one]
  rw [dotProduct]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hnot
    exact (hnot (Finset.mem_univ i)).elim

/-- Jensen for a finite probability vector and the convex function `x ↦ x^k`
on the nonnegative real half-line. -/
theorem lower_weighted_pow_le_sum
    {ι : Type*} [Fintype ι] (lam w : ι → ℝ) (k : ℕ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * lam i) ^ k ≤ ∑ i, w i * (lam i ^ k) := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ k) :=
    convexOn_pow k
  have h :=
    hconv.map_sum_le
      (t := (Finset.univ : Finset ι))
      (w := w) (p := lam)
      (by intro i _hi; exact hw i)
      (by simpa using hsum)
      (by intro i _hi; exact hlam i)
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- The squared coordinates of a unitary image of a unit vector sum to one. -/
theorem lower_unitary_coordinate_weight_sum_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : ↥(unitary (Matrix n n ℂ))) (z : EuclideanSpace ℂ n)
    (hz : ‖z‖ = 1) :
    ∑ j : n,
      ‖((PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
          (star U)) z).ofLp j‖ ^ 2 = 1 := by
  have hnorm :
      ‖(PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
          (star U)) z‖ = 1 := by
    simpa [hz] using
      (PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
        (star U)).norm_map z
  have hsquares :
      ‖(PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
          (star U)) z‖ ^ 2 =
        ∑ j : n,
          ‖((PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
              (star U)) z).ofLp j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  nlinarith

/-- Closed proof of the positive-semidefinite diagonal/trace-power core.

This is pure finite-dimensional spectral bookkeeping: diagonal entries are
convex averages of nonnegative eigenvalues, and the trace power is the sum of
the corresponding eigenvalue powers. -/
theorem lowerPosSemidefDiagonalPowerLeTracePowerCore_closed
    (k : ℕ) :
    lowerPosSemidefDiagonalPowerLeTracePowerCore k := by
  intro d hd ρ hρ
  let i₀ : Fin d := ⟨0, hd⟩
  change ((ρ i₀ i₀).re) ^ k ≤ ((Matrix.trace (ρ ^ k)).re)
  let hHerm : ρ.IsHermitian := hρ.1
  let U := hHerm.eigenvectorUnitary
  let z : EuclideanSpace ℂ (Fin d) :=
    coordinateUnitVector (ι := Fin d) i₀
  let weight : Fin d → ℝ :=
    fun j =>
      ‖(PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
          (star U) z) j‖ ^ 2
  have hz_norm : ‖z‖ = 1 := by
    simpa [z] using norm_coordinateUnitVector (ι := Fin d) i₀
  have hweight_nonneg : ∀ j, 0 ≤ weight j := by
    intro j
    dsimp [weight]
    positivity
  have hweight_sum : ∑ j : Fin d, weight j = 1 := by
    simpa [weight, z, U] using lower_unitary_coordinate_weight_sum_one U z hz_norm
  have hweight_le_one : ∀ j : Fin d, weight j ≤ 1 := by
    intro j
    calc
      weight j ≤ ∑ x : Fin d, weight x := by
        exact Finset.single_le_sum (fun x _ => hweight_nonneg x) (Finset.mem_univ j)
      _ = 1 := hweight_sum
  have heig_nonneg : ∀ j : Fin d, 0 ≤ hHerm.eigenvalues j := by
    intro j
    exact hρ.eigenvalues_nonneg j
  have hdiag_q :
      (ρ i₀ i₀).re = HighDimensionalProbability.quadraticForm ρ z := by
    rw [lower_quadraticForm_coordinateUnitVector_eq_diag_re]
  have hdiag_spectral :
      (ρ i₀ i₀).re =
        ∑ j : Fin d, weight j * hHerm.eigenvalues j := by
    calc
      (ρ i₀ i₀).re = HighDimensionalProbability.quadraticForm ρ z := hdiag_q
      _ =
          HighDimensionalProbability.quadraticForm
            (((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)) U)
              (Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues))) z := by
            exact congrArg (fun M => HighDimensionalProbability.quadraticForm M z)
              hHerm.spectral_theorem
      _ =
          HighDimensionalProbability.quadraticForm
            (Matrix.diagonal (fun j : Fin d => ((hHerm.eigenvalues j : ℝ) : ℂ)))
            (PptFactorization.HighProbabilityBounds.matrixUnitaryLinearIsometryEquiv
              (star U) z) := by
            simpa [U] using
              PptFactorization.HighProbabilityBounds.quadraticForm_conjStarAlgAut_diagonal
                (U := U) (h := hHerm.eigenvalues) z
      _ = ∑ j : Fin d, hHerm.eigenvalues j * weight j := by
            rw [PptFactorization.HighProbabilityBounds.quadraticForm_diagonal_real]
      _ = ∑ j : Fin d, weight j * hHerm.eigenvalues j := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
  have hjensen :
      (∑ j : Fin d, weight j * hHerm.eigenvalues j) ^ k ≤
        ∑ j : Fin d, weight j * (hHerm.eigenvalues j ^ k) :=
    lower_weighted_pow_le_sum hHerm.eigenvalues weight k heig_nonneg hweight_nonneg
      hweight_sum
  have hweighted_le :
      ∑ j : Fin d, weight j * (hHerm.eigenvalues j ^ k) ≤
        ∑ j : Fin d, hHerm.eigenvalues j ^ k := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    simpa using
      mul_le_mul_of_nonneg_right (hweight_le_one j)
        (pow_nonneg (heig_nonneg j) k)
  have htrace :
      ((Matrix.trace (ρ ^ k)).re) =
        ∑ j : Fin d, hHerm.eigenvalues j ^ k :=
    hermitian_re_trace_pow_eq_sum_eigenvalues_pow ρ hHerm k
  calc
    ((ρ i₀ i₀).re) ^ k =
        (∑ j : Fin d, weight j * hHerm.eigenvalues j) ^ k := by
          rw [hdiag_spectral]
    _ ≤ ∑ j : Fin d, weight j * (hHerm.eigenvalues j ^ k) := hjensen
    _ ≤ ∑ j : Fin d, hHerm.eigenvalues j ^ k := hweighted_le
    _ = (Matrix.trace (ρ ^ k)).re := htrace.symm

/-- If the matrix-only positive-semidefinite diagonal/trace-power core is
available, then the left-density diagonal-power frontier follows immediately by
instantiating `ρ = lowerLeftReducedDensity u`. -/
theorem lowerLeftReducedDensityDiagonalPowerLeTracePower_of_posSemidefCore
    {k : ℕ}
    (hCore : lowerPosSemidefDiagonalPowerLeTracePowerCore k) :
    lowerLeftReducedDensityDiagonalPowerLeTracePower k := by
  intro d hd u _hUnit
  simpa using hCore d hd
    (lowerLeftReducedDensity u)
    (lowerLeftReducedDensity_posSemidef (d := d) u)

/-- Closed proof of the first split unit-profile component. -/
theorem lowerLeftReducedDensityDiagonalPowerLeTracePower_closed
    (k : ℕ) :
    lowerLeftReducedDensityDiagonalPowerLeTracePower k :=
  lowerLeftReducedDensityDiagonalPowerLeTracePower_of_posSemidefCore
    (lowerPosSemidefDiagonalPowerLeTracePowerCore_closed k)

/-- Second split component of the left-density trace-power frontier:
the reduced-density trace power is bounded above by the partially-transposed
rank-one trace power. -/
def lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower
    (k : ℕ) : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d,
    ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
      ‖u‖ = 1 →
        let _i₀ : BipIndex (Fin d) (Fin d) :=
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
        let T : ℝ :=
          ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
              (p := Fin d) (q := Fin d) u) ^ k).trace.re
        0 ≤ T ∧
          ((Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re) ≤ T

/-- Matrix/bipartite core behind
`lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower`,
with the unused distinguished coordinate removed from the statement. -/
def lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore
    (k : ℕ) : Prop :=
  ∀ d : ℕ,
    ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
      ‖u‖ = 1 →
        let T : ℝ :=
          ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
              (p := Fin d) (q := Fin d) u) ^ k).trace.re
        0 ≤ T ∧
          ((Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re) ≤ T

/-- Elementary finite-sum bound: the sum of squares is bounded by the square of
the sum for nonnegative entries. -/
theorem lower_sum_sq_le_sum_sq
    {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    ∑ i, f i ^ 2 ≤ (∑ i, f i) ^ 2 := by
  calc
    ∑ i, f i ^ 2 ≤ ∑ i, f i * (∑ j, f j) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hle : f i ≤ ∑ j, f j :=
        Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)
      nlinarith [hf i, hle]
    _ = (∑ i, f i) ^ 2 := by
      rw [← Finset.sum_mul]
      ring

/-- The trace of a Hermitian power is a real complex number. -/
theorem lower_trace_of_hermitian_power_real
    {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.IsHermitian) (n : ℕ) :
    Matrix.trace (ρ ^ n) = (((Matrix.trace (ρ ^ n)).re : ℝ) : ℂ) := by
  have hpow : (ρ ^ n).IsHermitian := hρ.pow n
  have htrace := hpow.trace_eq_sum_eigenvalues
  rw [htrace]
  simp

/-- Even trace powers of the rank-one partial transpose dominate the
corresponding left-reduced-density trace powers. -/
theorem lower_rankOneProjectorGamma_even_trace_dominates_leftReducedDensity_trace
    {d : ℕ}
    (u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))) (p : ℕ) :
    ((Matrix.trace ((lowerLeftReducedDensity u) ^ (2 * p))).re) ≤
      ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
          (p := Fin d) (q := Fin d) u) ^ (2 * p)).trace.re := by
  let A : Matrix (Fin d) (Fin d) ℂ := lowerCoeffMatrix u
  let ρ : Matrix (Fin d) (Fin d) ℂ := A * Matrix.conjTranspose A
  let σ : Matrix (Fin d) (Fin d) ℂ := Matrix.conjTranspose A * A
  have hleft : lowerLeftReducedDensity u = ρ := by
    simp [ρ, A, lowerLeftReducedDensity_eq_coeff_mul_conjTranspose]
  have hρpsd : ρ.PosSemidef := by
    dsimp [ρ]
    simpa using (Matrix.posSemidef_self_mul_conjTranspose (A := A))
  let hρHerm : ρ.IsHermitian := hρpsd.1
  have heig_nonneg : ∀ i : Fin d, 0 ≤ hρHerm.eigenvalues i := by
    intro i
    exact hρpsd.eigenvalues_nonneg i
  let f : Fin d → ℝ := fun i => hρHerm.eigenvalues i ^ p
  have hf_nonneg : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    exact pow_nonneg (heig_nonneg i) p
  have hsum_sq := lower_sum_sq_le_sum_sq f hf_nonneg
  have htrace_left :
      ((Matrix.trace (ρ ^ (2 * p))).re) = ∑ i : Fin d, f i ^ 2 := by
    simpa [f, pow_mul, Nat.mul_comm, mul_comm, mul_assoc] using
      hermitian_re_trace_pow_eq_sum_eigenvalues_pow ρ hρHerm (2 * p)
  have htrace_p :
      ((Matrix.trace (ρ ^ p)).re) = ∑ i : Fin d, f i := by
    simpa [f] using hermitian_re_trace_pow_eq_sum_eigenvalues_pow ρ hρHerm p
  have hHtrace :
      ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
          (p := Fin d) (q := Fin d) u) ^ (2 * p)).trace =
        Matrix.trace (ρ ^ p) * Matrix.trace (σ ^ p) := by
    rw [lower_rankOneProjectorGamma_even_power_eq_kronecker_leftRight]
    rw [Matrix.trace_kronecker]
  have hσρ : Matrix.trace (σ ^ p) = Matrix.trace (ρ ^ p) := by
    simpa [ρ, σ] using (lower_trace_left_right_power_eq A p).symm
  have hρreal : Matrix.trace (ρ ^ p) = (((Matrix.trace (ρ ^ p)).re : ℝ) : ℂ) :=
    lower_trace_of_hermitian_power_real ρ hρHerm p
  calc
    ((Matrix.trace ((lowerLeftReducedDensity u) ^ (2 * p))).re)
        = ((Matrix.trace (ρ ^ (2 * p))).re) := by rw [hleft]
    _ = ∑ i : Fin d, f i ^ 2 := htrace_left
    _ ≤ (∑ i : Fin d, f i) ^ 2 := hsum_sq
    _ = ((Matrix.trace (ρ ^ p)).re) ^ 2 := by rw [htrace_p]
    _ = (Matrix.trace (ρ ^ p) * Matrix.trace (σ ^ p)).re := by
          rw [hσρ, hρreal]
          simp
          ring
    _ = ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
          (p := Fin d) (q := Fin d) u) ^ (2 * p)).trace.re := by
          rw [hHtrace]

/-- Closed proof of the rank-one partial-transpose trace-power dominance core.

Even powers use `tr(H^(2p)) = tr(ρ^p) tr(σ^p)` plus the Gram trace equality;
odd powers use the exact trace identity `tr(H^(2p+1)) = tr(ρ^(2p+1))`. -/
theorem lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore_closed
    (k : ℕ) :
    lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore k := by
  intro d u _hUnit
  let T : ℝ :=
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ k).trace.re
  have hρ_nonneg :
      0 ≤ (Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re :=
    lowerLeftReducedDensity_trace_pow_re_nonneg (d := d) u k
  rcases Nat.even_or_odd k with hEven | hOdd
  · rcases hEven with ⟨p, hk⟩
    have hk' : k = 2 * p := by omega
    have hdom :
        (Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re ≤ T := by
      subst hk'
      dsimp [T]
      exact lower_rankOneProjectorGamma_even_trace_dominates_leftReducedDensity_trace u p
    exact ⟨le_trans hρ_nonneg hdom, hdom⟩
  · rcases hOdd with ⟨p, hk⟩
    have hk' : k = 2 * p + 1 := by omega
    have hEq :
        (Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re = T := by
      subst hk'
      dsimp [T]
      exact congrArg Complex.re
        (lower_rankOneProjectorGamma_odd_trace_eq_leftReducedDensity_trace u p).symm
    exact ⟨by simpa [hEq] using hρ_nonneg, le_of_eq hEq⟩

/-- The coordinate-free core statement implies the original
left-reduced-density trace-power domination frontier. -/
theorem lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower_of_core
    {k : ℕ}
    (hCore :
      lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore k) :
    lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower k := by
  intro d hd u hUnit
  simpa using hCore d u hUnit

/-- Closed proof of the second split unit-profile component. -/
theorem lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower_closed
    (k : ℕ) :
    lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower k :=
  lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower_of_core
    (lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore_closed k)

/-- Exact Schmidt-side trace-power identity frontier.

This is the sharp local statement behind
`lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower`:
for a unit bipartite vector, the real trace power of the partial transpose of
the rank-one projector equals the real trace power of the left reduced density.
-/
def lowerRankOneProjectorGammaTracePowerEqLeftReducedDensityTracePower
    (k : ℕ) : Prop :=
  ∀ d : ℕ, ∀ hd : 0 < d,
    ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
      ‖u‖ = 1 →
        let _i₀ : BipIndex (Fin d) (Fin d) :=
          ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
        let T : ℝ :=
          ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
              (p := Fin d) (q := Fin d) u) ^ k).trace.re
        0 ≤ T ∧
          ((Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re) = T

/-- The exact Schmidt trace-power identity implies the second split component
used in the left-density diagonal-power frontier. -/
theorem lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower_of_eq
    {k : ℕ}
    (hEq : lowerRankOneProjectorGammaTracePowerEqLeftReducedDensityTracePower k) :
    lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower k := by
  intro d hd u hUnit
  rcases hEq d hd u hUnit with ⟨hT_nonneg, hTrace_eq_T⟩
  exact ⟨hT_nonneg, hTrace_eq_T.le⟩

/-- Closed bookkeeping from the split left-density trace-power components to
the single left-density diagonal-power frontier. -/
theorem lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_of_split
    {k : ℕ}
    (hDiag : lowerLeftReducedDensityDiagonalPowerLeTracePower k)
    (hTrace :
      lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower k) :
    lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k := by
  intro d hd u hUnit
  let i₀ : BipIndex (Fin d) (Fin d) :=
    ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
  let T : ℝ :=
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ k).trace.re
  have hDiag_le_trace :
      ((lowerLeftReducedDensity u) i₀.1 i₀.1).re ^ k ≤
        (Matrix.trace ((lowerLeftReducedDensity u) ^ k)).re :=
    hDiag d hd u hUnit
  rcases hTrace d hd u hUnit with ⟨hT_nonneg, hTrace_le_T⟩
  exact ⟨hT_nonneg, le_trans hDiag_le_trace hTrace_le_T⟩

/-- Matrix-core decomposition of the left-density diagonal-power frontier.

To close `hLeftDensity`, it is enough to prove:

1. a positive-semidefinite matrix diagonal/trace-power inequality
   (`lowerPosSemidefDiagonalPowerLeTracePowerCore`);
2. the rank-one-Γ trace-power lower bound by the reduced-density trace power
   (`lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore`).
-/
theorem lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_of_cores
    {k : ℕ}
    (hDiagCore : lowerPosSemidefDiagonalPowerLeTracePowerCore k)
    (hTraceCore :
      lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore k) :
    lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k := by
  exact
    lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_of_split
      (lowerLeftReducedDensityDiagonalPowerLeTracePower_of_posSemidefCore hDiagCore)
      (lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePower_of_core
        hTraceCore)

/-- Closed left-density diagonal-power trace frontier from the two finite
matrix cores. -/
theorem lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed
    (k : ℕ) :
    lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k := by
  exact
    lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_of_cores
      (lowerPosSemidefDiagonalPowerLeTracePowerCore_closed k)
      (lowerRankOneProjectorGammaTracePowerDominatesLeftReducedDensityTracePowerCore_closed k)

/-- Closed reduction from the left-reduced-density trace-power frontier to the
coordinate-overlap `hTraceDominance` frontier. -/
theorem lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
    {k : ℕ}
    (hLeft :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k) :
    lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k := by
  intro d hd u hUnit
  let i₀ : BipIndex (Fin d) (Fin d) :=
    ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
  let T : ℝ :=
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ k).trace.re
  rcases hLeft d hd u hUnit with ⟨hT_nonneg, hDiag_le_T⟩
  refine ⟨hT_nonneg, ?_⟩
  exact le_trans
    (lower_coordinate_overlap_pow_le_leftReducedDensity_diag_re_pow
      (p := Fin d) (q := Fin d) u i₀ k)
    hDiag_le_T

/-- Closed coordinate-overlap trace dominance. -/
theorem lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_closed
    (k : ℕ) :
    lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k := by
  exact
    lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)

/-- Concrete scalar half of the canonical cap unit-profile budget.

For fixed `a`, the cap loss is `O_a(d^-4)`, while the concrete profile error is
`d^-1`; hence the scalar loss is eventually absorbed. -/
theorem lowerConcreteCanonicalCapProfileScalarBudget_concreteChoices
    {k : ℕ} {ε : ℝ} (hk : 1 < k) (hε : 0 < ε) :
    lowerConcreteCanonicalCapProfileScalarBudget k ε := by
  intro a ha slack hslack
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk0 hε) ha
  have ha_pow_nonneg : 0 ≤ a ^ k := pow_nonneg (le_of_lt ha_pos) k
  have hcube_atTop :
      Tendsto (fun d : ℕ => (d : ℝ) ^ 3) atTop atTop := by
    have hlin : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hsq : Tendsto (fun d : ℕ => (d : ℝ) * (d : ℝ)) atTop atTop :=
      hlin.atTop_mul_atTop₀ hlin
    simpa [pow_succ, pow_two, mul_assoc] using
      hsq.atTop_mul_atTop₀ hlin
  have hbig :
      ∀ᶠ d : ℕ in atTop, a ^ k * (k : ℝ) ≤ (d : ℝ) ^ 3 :=
    hcube_atTop.eventually_ge_atTop (a ^ k * (k : ℝ))
  filter_upwards [hbig, eventually_gt_atTop 0] with d hbig_d hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  let x : ℝ := (1 / (lowerConcreteNcap d : ℝ)) ^ 2
  have hx_eq : x = ((d : ℝ) ^ 4)⁻¹ := by
    dsimp [x]
    simp [Nat.cast_pow]
    field_simp [ne_of_gt hdR]
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hNcap_ge_one : 1 ≤ (lowerConcreteNcap d : ℝ) := by
    have hd_ge_one : (1 : ℝ) ≤ d := by exact_mod_cast hd
    simp [lowerConcreteNcap, Nat.cast_pow]
    nlinarith [hd_ge_one]
  have hx_le_one : x ≤ 1 := by
    have hfrac_nonneg : 0 ≤ 1 / (lowerConcreteNcap d : ℝ) := by
      positivity
    have hfrac_le_one : 1 / (lowerConcreteNcap d : ℝ) ≤ 1 := by
      exact div_le_one_of_le₀ hNcap_ge_one (by positivity)
    dsimp [x]
    simpa [pow_two] using
      mul_le_mul hfrac_le_one hfrac_le_one hfrac_nonneg zero_le_one
  have hBern : 1 + (k : ℝ) * (-x) ≤ (1 + (-x)) ^ k := by
    exact one_add_mul_le_pow (by linarith : -2 ≤ -x) k
  have hBern' : 1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
    simpa [sub_eq_add_neg, mul_neg] using hBern
  have hterm_le : 1 - (1 - x) ^ k ≤ (k : ℝ) * x := by
    linarith
  have hscaled :
      a ^ k * ((k : ℝ) * x) ≤ lowerConcreteProfileError k ε a slack d := by
    calc
      a ^ k * ((k : ℝ) * x)
          = (a ^ k * (k : ℝ)) / ((d : ℝ) ^ 4) := by
              rw [hx_eq]
              field_simp [ne_of_gt (pow_pos hdR 4)]
      _ ≤ ((d : ℝ) ^ 3) / ((d : ℝ) ^ 4) := by
              exact div_le_div_of_nonneg_right hbig_d
                (le_of_lt (pow_pos hdR 4))
      _ = 1 / (d : ℝ) := by
              field_simp [ne_of_gt hdR]
      _ = lowerConcreteProfileError k ε a slack d := by
              simp [lowerConcreteProfileError, lowerConcreteDelta]
  have hloss :
      a ^ k * (1 - (1 - x) ^ k) ≤
        lowerConcreteProfileError k ε a slack d := by
    calc
      a ^ k * (1 - (1 - x) ^ k)
          ≤ a ^ k * ((k : ℝ) * x) :=
              mul_le_mul_of_nonneg_left hterm_le ha_pow_nonneg
      _ ≤ lowerConcreteProfileError k ε a slack d := hscaled
  have hrearrange :
      a ^ k - a ^ k * (1 - x) ^ k ≤
        lowerConcreteProfileError k ε a slack d := by
    calc
      a ^ k - a ^ k * (1 - x) ^ k
          = a ^ k * (1 - (1 - x) ^ k) := by ring
      _ ≤ lowerConcreteProfileError k ε a slack d := hloss
  have htarget :
      a ^ k - lowerConcreteProfileError k ε a slack d ≤
        a ^ k * (1 - x) ^ k := by
    linarith
  simpa [x] using htarget

/-- Closed cap algebra from coordinate-overlap trace dominance to the canonical
cap trace-overlap frontier. -/
theorem lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
    {k : ℕ}
    (hDominates :
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k) :
    lowerConcreteCanonicalCapTracePowerOverlapLower k := by
  intro a slack
  filter_upwards [eventually_gt_atTop 0] with d hd
  intro u hCap hUnit
  let i₀ : BipIndex (Fin d) (Fin d) :=
    ((⟨0, hd⟩ : Fin d), (⟨0, hd⟩ : Fin d))
  let T : ℝ :=
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ k).trace.re
  rcases hDominates d hd u hUnit with ⟨hT_nonneg, hCoord_le_T⟩
  refine ⟨hT_nonneg, ?_⟩
  have hCapOverlap :
      1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2 ≤
        ‖inner ℂ
          (coordinateUnitVector
            (ι := BipIndex (Fin d) (Fin d)) i₀)
          u‖ ^ 2 := by
    simpa [i₀] using
      lower_canonicalDirection_cap_inner_sq_ge
        (a := a) (slack := slack) hd hCap
  have hNcap_ge_one : 1 ≤ (lowerConcreteNcap d : ℝ) := by
    have hd_ge_one : (1 : ℝ) ≤ d := by exact_mod_cast hd
    simp [lowerConcreteNcap, Nat.cast_pow]
    nlinarith [hd_ge_one]
  have hr_nonneg : 0 ≤ 1 / (lowerConcreteNcap d : ℝ) := by positivity
  have hr_le_one : 1 / (lowerConcreteNcap d : ℝ) ≤ 1 := by
    exact div_le_one_of_le₀ hNcap_ge_one (by positivity)
  have hr_sq_le_one : (1 / (lowerConcreteNcap d : ℝ)) ^ 2 ≤ 1 := by
    simpa [pow_two] using
      mul_le_mul hr_le_one hr_le_one hr_nonneg zero_le_one
  have hbase_nonneg :
      0 ≤ 1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2 := by
    linarith
  have hpow_le :
      (1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2) ^ k ≤
        (‖inner ℂ
          (coordinateUnitVector
            (ι := BipIndex (Fin d) (Fin d)) i₀)
          u‖ ^ 2) ^ k :=
    pow_le_pow_left₀ hbase_nonneg hCapOverlap k
  calc
    (1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2) ^ k
        ≤ (‖inner ℂ
          (coordinateUnitVector
            (ι := BipIndex (Fin d) (Fin d)) i₀)
          u‖ ^ 2) ^ k := hpow_le
    _ = ‖inner ℂ
          (coordinateUnitVector
            (ι := BipIndex (Fin d) (Fin d)) i₀)
          u‖ ^ (2 * k) := by
          rw [pow_mul]
    _ ≤ T := hCoord_le_T

/-- Closed bookkeeping from the split cap-overlap and scalar-budget inputs to
the exact trace-stability frontier. -/
theorem lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower_and_scalarBudget
    {k : ℕ} {ε : ℝ} (hk : 1 < k) (hε : 0 < ε)
    (hOverlap : lowerConcreteCanonicalCapTracePowerOverlapLower k)
    (hScalar : lowerConcreteCanonicalCapProfileScalarBudget k ε) :
    lowerConcreteCanonicalCapSpikeTraceStability k ε := by
  intro a ha slack hslack
  filter_upwards [hOverlap a slack, hScalar a ha slack hslack,
    eventually_gt_atTop 0] with d hOverlap_d hScalar_d hd
  intro u hCap hUnit
  let q0 : ℝ :=
    betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a
  let T : ℝ :=
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ k).trace.re
  rcases hOverlap_d u hCap hUnit with ⟨hT_nonneg, hCapPow_le_T⟩
  refine ⟨hT_nonneg, ?_⟩
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk0 hε) ha
  have ha_pow_nonneg : 0 ≤ a ^ k := pow_nonneg (le_of_lt ha_pos) k
  have hscale :
      (lowerConcreteN d : ℝ) ^ (k - 1) * q0 ^ k = a ^ k := by
    simpa [q0] using
      lowerConcreteN_mul_betaColumnSpikeScale_pow_eq
        (k := k) (d := d) hk0 hd a
  have hmul :
      a ^ k *
          (1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2) ^ k ≤
        a ^ k * T := by
    exact mul_le_mul_of_nonneg_left hCapPow_le_T ha_pow_nonneg
  calc
    a ^ k - lowerConcreteProfileError k ε a slack d
        ≤ a ^ k *
            (1 - (1 / (lowerConcreteNcap d : ℝ)) ^ 2) ^ k :=
          hScalar_d
    _ ≤ a ^ k * T := hmul
    _ = (lowerConcreteN d : ℝ) ^ (k - 1) * (q0 ^ k * T) := by
          rw [← hscale]
          ring

/-- The canonical cap trace-stability frontier after closing the scalar cap
budget.  The only remaining unit-profile input is the geometric trace-overlap
bound on the projective cap. -/
theorem lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
    {k : ℕ} {ε : ℝ} (hk : 1 < k) (hε : 0 < ε)
    (hOverlap : lowerConcreteCanonicalCapTracePowerOverlapLower k) :
    lowerConcreteCanonicalCapSpikeTraceStability k ε :=
  lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower_and_scalarBudget
    hk hε hOverlap
    (lowerConcreteCanonicalCapProfileScalarBudget_concreteChoices hk hε)

/-- Closed bookkeeping from the cap trace-stability input to the full
pointwise unit-profile estimate. -/
theorem lower_columnDirectionSpikeProfile_canonicalCap_of_traceStability
    {k : ℕ} {ε a slack Rmass : ℝ} {d : ℕ}
    (hk : 1 < k) (hε : 0 < ε) (hd : 0 < d)
    (ha : spikeRoot k ε < a)
    (hMassLower :
      betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a ≤ Rmass)
    {u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d))}
    (hTrace :
      let q0 : ℝ :=
        betaColumnSpikeScale
          (lowerConcreteN d : ℝ) (spikeSpeed k d) a
      let T : ℝ :=
        ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
            (p := Fin d) (q := Fin d) u) ^ k).trace.re
      0 ≤ T ∧
        a ^ k - lowerConcreteProfileError k ε a slack d ≤
          (lowerConcreteN d : ℝ) ^ (k - 1) * (q0 ^ k * T)) :
    a ^ k - lowerConcreteProfileError k ε a slack d ≤
      columnDirectionSpikeProfile
        (p := Fin d) (q := Fin d)
        (lowerConcreteN d) k Rmass u := by
  let q0 : ℝ :=
    betaColumnSpikeScale (lowerConcreteN d : ℝ) (spikeSpeed k d) a
  let T : ℝ :=
    ((PptFactorization.HighProbabilityBounds.rankOneProjectorGamma
        (p := Fin d) (q := Fin d) u) ^ k).trace.re
  rcases hTrace with ⟨hT_nonneg, hTraceLower⟩
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  have ha_pos : 0 < a := lt_trans (spikeRoot_pos hk0 hε) ha
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hq0_pos : 0 < q0 := by
    have hNpos : 0 < (lowerConcreteN d : ℝ) := by
      simp [lowerConcreteN, pow_two, mul_pos hdR hdR]
    have hspeed : 0 < spikeSpeed k d := by
      simp [spikeSpeed, Real.rpow_pos_of_pos hdR]
    dsimp [q0, betaColumnSpikeScale]
    exact div_pos (mul_pos ha_pos hspeed) (sq_pos_of_pos hNpos)
  have hpow_le : q0 ^ k ≤ Rmass ^ k :=
    pow_le_pow_left₀ (le_of_lt hq0_pos) hMassLower k
  have hNpow_nonneg : 0 ≤ (lowerConcreteN d : ℝ) ^ (k - 1) := by
    positivity
  have hscaled_le :
      (lowerConcreteN d : ℝ) ^ (k - 1) * (q0 ^ k * T) ≤
        (lowerConcreteN d : ℝ) ^ (k - 1) * (Rmass ^ k * T) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow_le hT_nonneg)
      hNpow_nonneg
  have hprofile :
      columnDirectionSpikeProfile
          (p := Fin d) (q := Fin d)
          (lowerConcreteN d) k Rmass u =
        (lowerConcreteN d : ℝ) ^ (k - 1) * (Rmass ^ k * T) := by
    dsimp [T]
    unfold columnDirectionSpikeProfile pureSpikeContribution
    ring
  calc
    a ^ k - lowerConcreteProfileError k ε a slack d
        ≤ (lowerConcreteN d : ℝ) ^ (k - 1) * (q0 ^ k * T) :=
          hTraceLower
    _ ≤ (lowerConcreteN d : ℝ) ^ (k - 1) * (Rmass ^ k * T) :=
          hscaled_le
    _ = columnDirectionSpikeProfile
          (p := Fin d) (q := Fin d)
          (lowerConcreteN d) k Rmass u := hprofile.symm

/-- Conditional canonical unit-profile supplier from the exact cap-trace
stability frontier.  This theorem contains no project-specific proof debt; it
only exposes the smaller trace-stability statement above. -/
theorem lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability :
    ∀ {k : ℕ} {ε : ℝ}, 1 < k → 0 < ε →
      lowerConcreteCanonicalCapSpikeTraceStability k ε →
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u := by
  intro k ε hk hε hTraceStability a ha slack hslack
  filter_upwards [hTraceStability a ha slack hslack, eventually_gt_atTop 0]
    with d hTrace_d hd
  intro Rmass u hMass hCap hUnit
  exact
    lower_columnDirectionSpikeProfile_canonicalCap_of_traceStability
      (k := k) (ε := ε) (a := a) (slack := slack)
      (Rmass := Rmass) (d := d) hk hε
      hd
      ha
      (lower_betaColumnIntervalSet_left_le hMass)
      (hTrace_d u hCap hUnit)

/-- Conditional canonical unit-profile supplier from the split cap-overlap and
scalar-budget inputs.  This avoids the older pointwise theorem below, whose
all-dimension formulation is too coarse for the cap-loss budget. -/
theorem lower_unitProfile_canonicalDirection_concreteChoices_of_overlapLower_and_scalarBudget :
    ∀ {k : ℕ} {ε : ℝ}, 1 < k → 0 < ε →
      lowerConcreteCanonicalCapTracePowerOverlapLower k →
      lowerConcreteCanonicalCapProfileScalarBudget k ε →
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u := by
  intro k ε hk hε hOverlap hScalar
  exact
    lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
      hk hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower_and_scalarBudget
        hk hε hOverlap hScalar)

/-- Conditional canonical unit-profile supplier after closing the scalar
cap-loss budget.  This leaves only the geometric trace-overlap bound as visible
unit-profile debt. -/
theorem lower_unitProfile_canonicalDirection_concreteChoices_of_overlapLower :
    ∀ {k : ℕ} {ε : ℝ}, 1 < k → 0 < ε →
      lowerConcreteCanonicalCapTracePowerOverlapLower k →
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u := by
  intro k ε hk hε hOverlap
  exact
    lower_unitProfile_canonicalDirection_concreteChoices_of_traceStability
      hk hε
      (lowerConcreteCanonicalCapSpikeTraceStability_of_overlapLower
        hk hε hOverlap)

/-- Conditional canonical unit-profile supplier from the trace-dominance
frontier.  The cap algebra and scalar profile budget are closed here. -/
theorem lower_unitProfile_canonicalDirection_concreteChoices_of_traceDominatesCoordinateOverlap :
    ∀ {k : ℕ} {ε : ℝ}, 1 < k → 0 < ε →
      lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap k →
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u := by
  intro k ε hk hε hDominates
  exact
    lower_unitProfile_canonicalDirection_concreteChoices_of_overlapLower
      hk hε
      (lowerConcreteCanonicalCapTracePowerOverlapLower_of_traceDominatesCoordinateOverlap
        hDominates)

/-- Conditional canonical unit-profile supplier from the sharper left-density
trace-power frontier.  This closes the coordinate-overlap bookkeeping; the
remaining unit-profile math is the Schmidt/reduced-density trace-power
estimate. -/
theorem lower_unitProfile_canonicalDirection_concreteChoices_of_leftDensityDiagonalPower :
    ∀ {k : ℕ} {ε : ℝ}, 1 < k → 0 < ε →
      lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower k →
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u := by
  intro k ε hk hε hLeft
  exact
    lower_unitProfile_canonicalDirection_concreteChoices_of_traceDominatesCoordinateOverlap
      hk hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesCoordinateOverlap_of_leftDensityDiagonalPower
        hLeft)

/-- Closed canonical unit-profile supplier.

The trace-power part is now discharged by the left-density core proofs above;
the remaining work in this file is scalar Beta/cap bookkeeping already handled
by the previous wrappers. -/
theorem lower_unitProfile_canonicalDirection_concreteChoices :
    ∀ {k : ℕ} {ε : ℝ}, 1 < k → 0 < ε →
      ∀ a : ℝ, spikeRoot k ε < a →
        ∀ slack : ℝ, 0 < slack →
          ∀ᶠ d in atTop,
            ∀ Rmass : ℝ,
              ∀ u : EuclideanSpace ℂ (BipIndex (Fin d) (Fin d)),
                Rmass ∈
                  betaColumnIntervalSet
                    (betaColumnSpikeScale
                      (lowerConcreteN d : ℝ) (spikeSpeed k d) a)
                    (lowerConcreteDelta a slack d) →
                u ∈
                  lowerConcreteDirectionCapSet
                    lowerConcreteCanonicalDirection a slack d →
                ‖u‖ = 1 →
                a ^ k - lowerConcreteProfileError k ε a slack d ≤
                  columnDirectionSpikeProfile
                    (p := Fin d) (q := Fin d)
                    (lowerConcreteN d) k Rmass u := by
  intro k ε hk hε
  exact
    lower_unitProfile_canonicalDirection_concreteChoices_of_leftDensityDiagonalPower
      hk hε
      (lowerConcreteRankOneProjectorGammaTracePowerDominatesLeftDensityDiagonalPower_closed k)

/-!
Retired route.

The old direct no-input unit-profile theorem attempted to combine the Beta mass
lower bound and canonical-cap overlap in one step.  The live lower assembly no
longer depends on that route: it uses the sharper conditional suppliers above,
through `lowerConcreteCanonicalCapSpikeTraceStability`,
`lowerConcreteCanonicalCapTracePowerOverlapLower`, and the left-density
frontiers.
-/

end AppendixB
