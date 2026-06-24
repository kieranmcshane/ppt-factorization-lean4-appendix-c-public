import PptFactorization.AppendixBRadialSpherical
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# Appendix B: canonical surface measure on the Frobenius sphere

This file introduces the canonical surface measure on the Hilbert--Schmidt
unit sphere of sample matrices and imports Mathlib's genuine polar-coordinate
theorem for additive Haar measure.

The theorem proved here is the honest geometric polar-coordinate theorem:
Lebesgue/Haar measure on the punctured sample-matrix space is transported by
`homeomorphUnitSphereProd` to surface measure times the radial measure
`r^(N-1) dr`.

The further probabilistic statement

`law(G / ‖G‖₂) = normalized surface measure`

is the Gaussian polar-disintegration theorem.  It additionally needs the
standard multivariate Gaussian density with respect to this Haar measure (or an
equivalent no-input proof of radial/angular independence).  That theorem is not
asserted in this file.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal Pointwise

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## General uniqueness of invariant probability measures on compact homogeneous spaces -/

/-- The matrix unitary group carries the Borel measurable structure induced by
its subtype topology. -/
instance instMatrixUnitaryGroupMeasurableSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MeasurableSpace (Matrix.unitaryGroup ι ℂ) :=
  borel _

instance instMatrixUnitaryGroupBorelSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    BorelSpace (Matrix.unitaryGroup ι ℂ) :=
  ⟨rfl⟩

instance instMatrixUnitaryGroupOpensMeasurableSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    OpensMeasurableSpace (Matrix.unitaryGroup ι ℂ) := by
  infer_instance

instance instMatrixUnitaryGroupIsTopologicalGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsTopologicalGroup (Matrix.unitaryGroup ι ℂ) where
  continuous_mul := by
    let f : Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ → Matrix ι ι ℂ :=
      fun z => (z.1 : Matrix ι ι ℂ) * (z.2 : Matrix ι ι ℂ)
    have hf : Continuous f := by
      fun_prop
    exact hf.subtype_mk (fun z => by
      change ((z.1 : Matrix ι ι ℂ) * (z.2 : Matrix ι ι ℂ)) ∈ unitary (Matrix ι ι ℂ)
      exact (unitary (Matrix ι ι ℂ)).mul_mem z.1.2 z.2.2)
  continuous_inv := by
    let f : Matrix.unitaryGroup ι ℂ → Matrix ι ι ℂ := fun U => star (U : Matrix ι ι ℂ)
    have hf : Continuous f := by
      fun_prop
    exact hf.subtype_mk (fun U => by
      change star (U : Matrix ι ι ℂ) ∈ unitary (Matrix ι ι ℂ)
      exact Unitary.star_mem U.2)

/-- A concrete Frobenius-norm bound for unitary matrices, used only to put the
matrix unitary group inside a compact closed ball. -/
theorem matrixUnitaryGroup_frobenius_norm_le_card_rpow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    ‖(U : Matrix ι ι ℂ)‖ ≤
      (((Fintype.card ι : ℝ) * Fintype.card ι) : ℝ) ^ (1 / 2 : ℝ) := by
  have hentry : ∀ i j : ι, ‖(U : Matrix ι ι ℂ) i j‖ ≤ 1 := by
    intro i j
    exact le_trans
      (Matrix.norm_entry_le_entrywise_sup_norm (A := (U : Matrix ι ι ℂ)) (i := i) (j := j))
      (entrywise_sup_norm_bound_of_unitary U.2)
  have hentry_sq : ∀ i j : ι, ‖(U : Matrix ι ι ℂ) i j‖ ^ (2 : ℝ) ≤ 1 := by
    intro i j
    have h := hentry i j
    have h0 : 0 ≤ ‖(U : Matrix ι ι ℂ) i j‖ := norm_nonneg _
    have hmul : ‖(U : Matrix ι ι ℂ) i j‖ * ‖(U : Matrix ι ι ℂ) i j‖ ≤ 1 * 1 := by
      nlinarith
    simpa [pow_two] using hmul
  have hsum :
      ∑ i : ι, ∑ j : ι, ‖(U : Matrix ι ι ℂ) i j‖ ^ (2 : ℝ) ≤
        ∑ i : ι, ∑ j : ι, (1 : ℝ) := by
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry_sq i j
  rw [Matrix.frobenius_norm_def]
  show (∑ i : ι, ∑ j : ι, ‖(U : Matrix ι ι ℂ) i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (((Fintype.card ι : ℝ) * Fintype.card ι) : ℝ) ^ (1 / 2 : ℝ)
  have hnonneg : 0 ≤ ∑ i : ι, ∑ j : ι, ‖(U : Matrix ι ι ℂ) i j‖ ^ (2 : ℝ) := by
    positivity
  calc
    (∑ i : ι, ∑ j : ι, ‖(U : Matrix ι ι ℂ) i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∑ i : ι, ∑ j : ι, (1 : ℝ)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hnonneg hsum (by positivity)
    _ = (((Fintype.card ι : ℝ) * Fintype.card ι) : ℝ) ^ (1 / 2 : ℝ) := by
      simp [Finset.card_univ]

instance instMatrixUnitaryGroupCompactSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    CompactSpace (Matrix.unitaryGroup ι ℂ) := by
  let S : Set (Matrix ι ι ℂ) := Matrix.unitaryGroup ι ℂ
  let R : ℝ := (((Fintype.card ι : ℝ) * Fintype.card ι) : ℝ) ^ (1 / 2 : ℝ)
  haveI : ProperSpace (Matrix ι ι ℂ) := FiniteDimensional.proper ℂ (Matrix ι ι ℂ)
  apply isCompact_iff_compactSpace.mp
  have hclosed1 : IsClosed {A : Matrix ι ι ℂ | star A * A = 1} :=
    isClosed_eq (continuous_star.mul continuous_id) continuous_const
  have hclosed2 : IsClosed {A : Matrix ι ι ℂ | A * star A = 1} :=
    isClosed_eq (continuous_id.mul continuous_star) continuous_const
  have hS_closed : IsClosed S := by
    change IsClosed {A : Matrix ι ι ℂ | star A * A = 1 ∧ A * star A = 1}
    exact hclosed1.inter hclosed2
  have hS_subset : S ⊆ Metric.closedBall (0 : Matrix ι ι ℂ) R := by
    intro U hU
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    simpa [R] using
      matrixUnitaryGroup_frobenius_norm_le_card_rpow (ι := ι) ⟨U, hU⟩
  exact (isCompact_closedBall (0 : Matrix ι ι ℂ) R).of_isClosed_subset hS_closed hS_subset

/-- The canonical left action of the matrix unitary group on the complex unit
sphere. -/
instance instMatrixUnitaryGroupSphereSMul
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    SMul (Matrix.unitaryGroup ι ℂ) (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) where
  smul U x :=
    ⟨WithLp.toLp 2 (fun i => ∑ j, (U : Matrix ι ι ℂ) i j * (x : EuclideanSpace ℂ ι) j), by
      simpa [Matrix.ofLp_toEuclideanCLM] using matrixUnitary_toEuclideanCLM_norm U x⟩

instance instMatrixUnitaryGroupSphereMulAction
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    MulAction (Matrix.unitaryGroup ι ℂ) (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) where
  one_smul := by
    intro x
    apply Subtype.ext
    ext i
    change (∑ j, (1 : Matrix ι ι ℂ) i j * ((x : EuclideanSpace ℂ ι) j)) =
      (x : EuclideanSpace ℂ ι) i
    simp [Matrix.one_apply]
  mul_smul := by
    intro U V x
    apply Subtype.ext
    ext i
    change (∑ j, ((U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) i j *
        ((x : EuclideanSpace ℂ ι) j)) =
      ∑ j, (U : Matrix ι ι ℂ) i j *
        (∑ k, (V : Matrix ι ι ℂ) j k * ((x : EuclideanSpace ℂ ι) k))
    calc
      _ = ∑ j, ∑ k,
          ((U : Matrix ι ι ℂ) i k * (V : Matrix ι ι ℂ) k j) *
            ((x : EuclideanSpace ℂ ι) j) := by
            simp [Matrix.mul_apply, Finset.sum_mul]
      _ = ∑ j, ∑ k,
          (U : Matrix ι ι ℂ) i j *
            ((V : Matrix ι ι ℂ) j k * ((x : EuclideanSpace ℂ ι) k)) := by
            rw [Finset.sum_comm]
            simp [mul_assoc]
      _ = ∑ j, (U : Matrix ι ι ℂ) i j *
          (∑ k, (V : Matrix ι ι ℂ) j k * ((x : EuclideanSpace ℂ ι) k)) := by
            simp [Finset.mul_sum]

instance instMatrixUnitaryGroupSphereContinuousSMul
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousSMul (Matrix.unitaryGroup ι ℂ) (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) where
  continuous_smul := by
    let f :
        Matrix.unitaryGroup ι ℂ × Metric.sphere (0 : EuclideanSpace ℂ ι) 1 →
          EuclideanSpace ℂ ι :=
      fun z => WithLp.toLp 2 (fun i => ∑ j, (z.1 : Matrix ι ι ℂ) i j *
        (z.2 : EuclideanSpace ℂ ι) j)
    have hf' :
        Continuous (fun z : Matrix.unitaryGroup ι ℂ × Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
          fun i => ∑ j, (z.1 : Matrix ι ι ℂ) i j *
            ((z.2 : EuclideanSpace ℂ ι) j)) := by
      refine continuous_pi ?_
      intro i
      apply continuous_finset_sum
      intro j _
      have hUi :
          Continuous
            (fun z : Matrix.unitaryGroup ι ℂ × Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
              (((z.1 : Matrix ι ι ℂ) i : ι → ℂ))) := by
        exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
      have hUij :
          Continuous
            (fun z : Matrix.unitaryGroup ι ℂ × Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
              ((((z.1 : Matrix ι ι ℂ) i : ι → ℂ)) j)) := by
        exact (continuous_apply j).comp hUi
      have hx0 :
          Continuous
            (fun z : Matrix.unitaryGroup ι ℂ × Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
              (z.2 : EuclideanSpace ℂ ι)) := by
        exact
          (@continuous_subtype_val (EuclideanSpace ℂ ι) _
            (fun x => x ∈ Metric.sphere (0 : EuclideanSpace ℂ ι) 1)).comp continuous_snd
      have hxj :
          Continuous
            (fun z : Matrix.unitaryGroup ι ℂ × Metric.sphere (0 : EuclideanSpace ℂ ι) 1 =>
              ((((z.2 : EuclideanSpace ℂ ι) : ι → ℂ)) j)) := by
        simpa using
          (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℂ) j).comp hx0
      exact hUij.mul hxj
    have hf : Continuous f := by
      simpa [f] using (PiLp.continuous_toLp 2 _).comp hf'
    exact hf.subtype_mk (fun z => by
      simpa [f, Matrix.ofLp_toEuclideanCLM] using matrixUnitary_toEuclideanCLM_norm z.1 z.2)

/-- The matrix unitary group acts pretransitively on the complex unit sphere:
every unit vector can be moved to every other by a unitary. -/
instance instMatrixUnitaryGroupSpherePretransitive
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    MulAction.IsPretransitive (Matrix.unitaryGroup ι ℂ)
      (Metric.sphere (0 : EuclideanSpace ℂ ι) 1) := by
  classical
  refine ⟨?_⟩
  intro x y
  let i0 : ι := Classical.choice ‹Nonempty ι›
  let vx : ι → EuclideanSpace ℂ ι := fun i => if i = i0 then x else 0
  let vy : ι → EuclideanSpace ℂ ι := fun i => if i = i0 then y else 0
  have hvx : Orthonormal ℂ (({i0} : Set ι).restrict vx) := by
    refine ⟨?_, ?_⟩
    · intro a
      have ha : ((a : ({i0} : Set ι)) : ι) = i0 := Set.mem_singleton_iff.mp a.2
      have hx : ‖(x : EuclideanSpace ℂ ι)‖ = 1 := by
        rw [← dist_zero_right (a := (x : EuclideanSpace ℂ ι))]
        change (x : EuclideanSpace ℂ ι) ∈ Metric.sphere (0 : EuclideanSpace ℂ ι) 1
        exact x.2
      change ‖vx a‖ = 1
      rw [ha]
      simp [vx, hx]
    · intro a b hab
      exact False.elim (hab (Subsingleton.elim a b))
  have hvy : Orthonormal ℂ (({i0} : Set ι).restrict vy) := by
    refine ⟨?_, ?_⟩
    · intro a
      have ha : ((a : ({i0} : Set ι)) : ι) = i0 := Set.mem_singleton_iff.mp a.2
      have hy : ‖(y : EuclideanSpace ℂ ι)‖ = 1 := by
        rw [← dist_zero_right (a := (y : EuclideanSpace ℂ ι))]
        change (y : EuclideanSpace ℂ ι) ∈ Metric.sphere (0 : EuclideanSpace ℂ ι) 1
        exact y.2
      change ‖vy a‖ = 1
      rw [ha]
      simp [vy, hy]
    · intro a b hab
      exact False.elim (hab (Subsingleton.elim a b))
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := by
    exact Module.finrank_eq_card_basis (EuclideanSpace.basisFun ι ℂ).toBasis
  obtain ⟨bx, hbx⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) hcard hvx
  obtain ⟨byBasis, hby⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := EuclideanSpace ℂ ι) hcard hvy
  let F : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    bx.equiv byBasis (Equiv.refl ι)
  have hFx : F x = y := by
    have hbx0 : bx i0 = x := by
      simpa [vx] using hbx i0 (by simp)
    have hby0 : byBasis i0 = y := by
      simpa [vy] using hby i0 (by simp)
    rw [← hbx0, OrthonormalBasis.equiv_apply_basis]
    simpa using hby0
  let uCLM : unitary (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
    Unitary.linearIsometryEquiv.symm F
  let Umat : Matrix ι ι ℂ := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm) uCLM
  have hUmat : Umat ∈ Matrix.unitaryGroup ι ℂ := by
    change Umat ∈ unitary (Matrix ι ι ℂ)
    exact Unitary.map_mem ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm) uCLM.2
  refine ⟨⟨Umat, hUmat⟩, ?_⟩
  apply Subtype.ext
  change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) Umat x = y
  simpa [Umat] using hFx

/-- If a compact group acts continuously and pretransitively on a compact Hausdorff space, then
two invariant probability measures on that space are equal.

This is the reusable “Haar uniqueness on a compact homogeneous space” lemma needed downstream for
direction laws on spheres: once two candidate probability measures are both invariant under the same
transitive compact action, they coincide. -/
theorem invariant_probabilityMeasure_eq_of_compact_pretransitive
    {G X : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [OpensMeasurableSpace G] [CompactSpace G]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace X] [CompactSpace X]
    [MulAction G X] [ContinuousSMul G X] [MeasurableConstSMul G X]
    [MulAction.IsPretransitive G X]
    (μ σ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure σ]
    [μ.Regular] [σ.Regular]
    (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (hσ : ∀ g : G, MeasurePreserving (fun x : X => g • x) σ σ) :
    μ = σ := by
  classical
  let m : Measure G := Measure.haar
  letI : SMulInvariantMeasure G X μ :=
    ⟨fun g _s hs =>
      MeasureTheory.Measure.measure_preimage_of_map_eq_self
        (hμ g).map_eq hs.nullMeasurableSet⟩
  letI : SMulInvariantMeasure G X σ :=
    ⟨fun g _s hs =>
      MeasureTheory.Measure.measure_preimage_of_map_eq_self
        (hσ g).map_eq hs.nullMeasurableSet⟩
  have hm_nonempty : (Set.univ : Set G).Nonempty := ⟨1, by simp⟩
  have hm_ne_zero : m ≠ 0 := by
    refine fun hm0 => ?_
    have hpos : IsOpen (Set.univ : Set G) := isOpen_univ
    have hne : m Set.univ ≠ 0 := hpos.measure_ne_zero m hm_nonempty
    simp [hm0] at hne
  have hmR_ne : m.real Set.univ ≠ 0 := by
    letI : NeZero m := ⟨hm_ne_zero⟩
    exact measureReal_univ_ne_zero
  have hX_nonempty : Nonempty X := by
    by_contra hX
    letI : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
    have huniv : (Set.univ : Set X) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hX ⟨x⟩
    have hzero : (μ Set.univ) = 0 := by
      rw [huniv]
      simp
    have hprob : (μ Set.univ) = 1 := by simp
    rw [hzero] at hprob
    norm_num at hprob
  let x0 : X := Classical.choice hX_nonempty
  refine Measure.ext_of_integral_eq_on_compactlySupported ?_
  intro f
  let A : X → ℝ := fun x => ∫ g, f (g⁻¹ • x) ∂m
  have hA_const : ∀ x : X, A x = A x0 := by
    intro x
    rcases MulAction.exists_smul_eq G x0 x with ⟨h, rfl⟩
    dsimp [A]
    calc
      ∫ g, f (g⁻¹ • (h • x0)) ∂m = ∫ g, f ((h⁻¹ * g)⁻¹ • x0) ∂m := by
        congr with g
        simp [smul_smul]
      _ = ∫ g, f (g⁻¹ • x0) ∂m := by
        simpa using
          (integral_mul_left_eq_self (μ := m) (f := fun g : G => f (g⁻¹ • x0)) h⁻¹)
  have hfg_cont : Continuous (fun z : X × G => f (z.2⁻¹ • z.1)) := by
    exact f.continuous.comp (continuous_snd.inv.smul continuous_fst)
  have hfg_comp : HasCompactSupport (fun z : X × G => f (z.2⁻¹ • z.1)) := by
    exact HasCompactSupport.of_compactSpace _
  have hμ_avg : A x0 = m.real Set.univ * ∫ x, f x ∂μ := by
    calc
      A x0 = ∫ x, A x ∂μ := by
        symm
        calc
          ∫ x, A x ∂μ = ∫ x, A x0 ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hA_const
          _ = A x0 := by simp [A]
      _ = ∫ x, ∫ g, f (g⁻¹ • x) ∂m ∂μ := rfl
      _ = ∫ g, ∫ x, f (g⁻¹ • x) ∂μ ∂m := by
        simpa [Function.uncurry] using
          (integral_integral_swap_of_hasCompactSupport
            (f := fun x g => f (g⁻¹ • x)) hfg_cont hfg_comp
            (μ := μ) (ν := m))
      _ = ∫ g, ∫ x, f x ∂μ ∂m := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun g => by
          simpa using (integral_smul_eq_self (μ := μ) (f := fun x : X => f x) (g := g⁻¹))
      _ = m.real Set.univ * ∫ x, f x ∂μ := by
        simp [smul_eq_mul]
  have hσ_avg : A x0 = m.real Set.univ * ∫ x, f x ∂σ := by
    calc
      A x0 = ∫ x, A x ∂σ := by
        symm
        calc
          ∫ x, A x ∂σ = ∫ x, A x0 ∂σ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hA_const
          _ = A x0 := by simp [A]
      _ = ∫ x, ∫ g, f (g⁻¹ • x) ∂m ∂σ := rfl
      _ = ∫ g, ∫ x, f (g⁻¹ • x) ∂σ ∂m := by
        simpa [Function.uncurry] using
          (integral_integral_swap_of_hasCompactSupport
            (f := fun x g => f (g⁻¹ • x)) hfg_cont hfg_comp
            (μ := σ) (ν := m))
      _ = ∫ g, ∫ x, f x ∂σ ∂m := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun g => by
          simpa using (integral_smul_eq_self (μ := σ) (f := fun x : X => f x) (g := g⁻¹))
      _ = m.real Set.univ * ∫ x, f x ∂σ := by
        simp [smul_eq_mul]
  have hEq : m.real Set.univ * ∫ x, f x ∂μ = m.real Set.univ * ∫ x, f x ∂σ := by
    rw [← hμ_avg, ← hσ_avg]
  exact (mul_left_cancel₀ hmR_ne) hEq

/-! ## Canonical surface measure -/

/-- Transport invariance for Mathlib's `Measure.toSphere` construction.

If a real linear isometry preserves the ambient additive Haar measure, then its
restriction to the unit sphere preserves the induced surface measure.  This is
the local, no-input replacement for the previously guessed
`surfaceMeasure_map_unitary`-style lemma. -/
theorem toSphere_map_linearIsometryEquiv_of_map_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (Metric.sphere (0 : E) 1)]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (U : E ≃ₗᵢ[ℝ] E)
    (hμ : Measure.map U μ = μ) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        μ.toSphere = μ.toSphere := by
  let S : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1 :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_cont : Continuous S := by
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S := hS_cont.measurable
  apply MeasureTheory.ext_of_generate_finite
      ({s : Set (Metric.sphere (0 : E) 1) | IsOpen s})
      (BorelSpace.measurable_eq.trans
        (borel_eq_generateFrom_of_subbasis
          (TopologicalSpace.generateFrom_setOf_isOpen
            (inferInstance : TopologicalSpace (Metric.sphere (0 : E) 1))).symm))
      isPiSystem_isOpen
  · intro s hsOpen
    change IsOpen s at hsOpen
    have hs_meas : MeasurableSet s := hsOpen.measurableSet
    have hpre_open : IsOpen (S ⁻¹' s) := hsOpen.preimage hS_cont
    have hpre_meas : MeasurableSet (S ⁻¹' s) := hpre_open.measurableSet
    let cone : Set (Metric.sphere (0 : E) 1) → Set E :=
      fun t => Set.Ioo (0 : ℝ) 1 •
        ((Subtype.val : Metric.sphere (0 : E) 1 → E) '' t)
    have hcone_open : IsOpen (cone s) := by
      simpa [cone] using
        (isOpen_Ioo.smul_sphere (E := E) (r := (1 : ℝ)) one_ne_zero
          (by simp) hsOpen)
    have hcone_eq : cone (S ⁻¹' s) = U ⁻¹' cone s := by
      ext x
      constructor
      · rintro ⟨r, hr, _y, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨r, hr, (S u : E), ⟨S u, hu, rfl⟩, ?_⟩
        simp [S]
      · intro hx
        rcases hx with ⟨r, hr, _y, ⟨u, hu, rfl⟩, hEq⟩
        let v : Metric.sphere (0 : E) 1 :=
          ⟨U.symm (u : E), by
            have hmem : (u : E) ∈ Metric.sphere (0 : E) 1 := u.property
            simp at hmem ⊢⟩
        refine ⟨r, hr, (v : E), ⟨v, ?_, rfl⟩, ?_⟩
        · have hSv : S v = u := by
            ext
            simp [S, v]
          simpa [hSv] using hu
        · apply U.injective
          calc
            U (r • (v : E)) = r • (u : E) := by simp [v]
            _ = U x := hEq
    calc
      (Measure.map S μ.toSphere) s = μ.toSphere (S ⁻¹' s) := by
        rw [Measure.map_apply hS_meas hs_meas]
      _ = Module.finrank ℝ E * μ (cone (S ⁻¹' s)) := by
        rw [Measure.toSphere_apply' μ hpre_meas]
      _ = Module.finrank ℝ E * μ (U ⁻¹' cone s) := by rw [hcone_eq]
      _ = Module.finrank ℝ E * (Measure.map U μ) (cone s) := by
        rw [Measure.map_apply U.continuous.measurable hcone_open.measurableSet]
      _ = Module.finrank ℝ E * μ (cone s) := by rw [hμ]
      _ = μ.toSphere s := by
        rw [Measure.toSphere_apply' μ hs_meas]
  · rw [Measure.map_apply hS_meas MeasurableSet.univ]
    simp

/-- Transport formula for Mathlib's `Measure.toSphere` construction between
two linearly isometric finite-dimensional real normed spaces.

The ambient additive Haar measures need not use matching normalizations.  If
the push-forward Haar measure is `c • ν`, then the induced unnormalised
surface measures are also related by the same scalar.  The scalar disappears
after probability normalization; see
`map_toFinite_toSphere_linearIsometryEquiv_of_map_eq_smul` below. -/
theorem toSphere_map_linearIsometryEquiv_of_map_eq_smul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [SecondCountableTopology (Metric.sphere (0 : E) 1)]
    [SecondCountableTopology (Metric.sphere (0 : F) 1)]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure]
    (U : E ≃ₗᵢ[ℝ] F) {c : ℝ≥0∞}
    (hμ : Measure.map U μ = c • ν) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        μ.toSphere =
      c • ν.toSphere := by
  let S : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1 :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_cont : Continuous S := by
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S := hS_cont.measurable
  have hfinrank : Module.finrank ℝ E = Module.finrank ℝ F :=
    U.toLinearEquiv.finrank_eq
  apply MeasureTheory.ext_of_generate_finite
      ({s : Set (Metric.sphere (0 : F) 1) | IsOpen s})
      (BorelSpace.measurable_eq.trans
        (borel_eq_generateFrom_of_subbasis
          (TopologicalSpace.generateFrom_setOf_isOpen
            (inferInstance : TopologicalSpace (Metric.sphere (0 : F) 1))).symm))
      isPiSystem_isOpen
  · intro s hsOpen
    change IsOpen s at hsOpen
    have hs_meas : MeasurableSet s := hsOpen.measurableSet
    have hpre_open : IsOpen (S ⁻¹' s) := hsOpen.preimage hS_cont
    have hpre_meas : MeasurableSet (S ⁻¹' s) := hpre_open.measurableSet
    let coneE : Set (Metric.sphere (0 : E) 1) → Set E :=
      fun t => Set.Ioo (0 : ℝ) 1 •
        ((Subtype.val : Metric.sphere (0 : E) 1 → E) '' t)
    let coneF : Set (Metric.sphere (0 : F) 1) → Set F :=
      fun t => Set.Ioo (0 : ℝ) 1 •
        ((Subtype.val : Metric.sphere (0 : F) 1 → F) '' t)
    have hcone_open : IsOpen (coneF s) := by
      simpa [coneF] using
        (isOpen_Ioo.smul_sphere (E := F) (r := (1 : ℝ)) one_ne_zero
          (by simp) hsOpen)
    have hcone_eq : coneE (S ⁻¹' s) = U ⁻¹' coneF s := by
      ext x
      constructor
      · rintro ⟨r, hr, _y, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨r, hr, (S u : F), ⟨S u, hu, rfl⟩, ?_⟩
        simp [S]
      · intro hx
        rcases hx with ⟨r, hr, _y, ⟨u, hu, rfl⟩, hEq⟩
        let v : Metric.sphere (0 : E) 1 :=
          ⟨U.symm (u : F), by
            have hmem : (u : F) ∈ Metric.sphere (0 : F) 1 := u.property
            simp at hmem ⊢⟩
        refine ⟨r, hr, (v : E), ⟨v, ?_, rfl⟩, ?_⟩
        · have hSv : S v = u := by
            ext
            simp [S, v]
          simpa [hSv] using hu
        · apply U.injective
          calc
            U (r • (v : E)) = r • (u : F) := by simp [v]
            _ = U x := hEq
    calc
      (Measure.map S μ.toSphere) s = μ.toSphere (S ⁻¹' s) := by
        rw [Measure.map_apply hS_meas hs_meas]
      _ = Module.finrank ℝ E * μ (coneE (S ⁻¹' s)) := by
        rw [Measure.toSphere_apply' μ hpre_meas]
      _ = Module.finrank ℝ E * μ (U ⁻¹' coneF s) := by rw [hcone_eq]
      _ = Module.finrank ℝ E * (Measure.map U μ) (coneF s) := by
        rw [Measure.map_apply U.continuous.measurable hcone_open.measurableSet]
      _ = Module.finrank ℝ E * (c * ν (coneF s)) := by
        rw [hμ]
        simp
      _ = c * (Module.finrank ℝ F * ν (coneF s)) := by
        rw [hfinrank]
        ac_rfl
      _ = (c • ν.toSphere) s := by
        rw [Measure.smul_apply, Measure.toSphere_apply' ν hs_meas]
        simp [coneF, smul_eq_mul]
  · rw [Measure.map_apply hS_meas MeasurableSet.univ]
    have hpre_ball : U ⁻¹' Metric.ball (0 : F) 1 = Metric.ball (0 : E) 1 := by
      ext x
      simp [Metric.mem_ball, dist_eq_norm]
    calc
      μ.toSphere Set.univ = Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) := by
        rw [Measure.toSphere_apply_univ]
      _ = Module.finrank ℝ E * μ (U ⁻¹' Metric.ball (0 : F) 1) := by rw [hpre_ball]
      _ = Module.finrank ℝ E * (Measure.map U μ) (Metric.ball (0 : F) 1) := by
        rw [Measure.map_apply U.continuous.measurable Metric.isOpen_ball.measurableSet]
      _ = Module.finrank ℝ E * (c * ν (Metric.ball (0 : F) 1)) := by
        rw [hμ]
        simp
      _ = c * (Module.finrank ℝ F * ν (Metric.ball (0 : F) 1)) := by
        rw [hfinrank]
        ac_rfl
      _ = (c • ν.toSphere) Set.univ := by
        rw [Measure.smul_apply, Measure.toSphere_apply_univ]
        simp [smul_eq_mul]

/-- Mapping commutes with probability-normalizing a finite measure. -/
theorem map_toFinite_eq_toFinite_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [SFinite μ] [IsFiniteMeasure μ]
    {f : α → β} (hf : Measurable f) :
    Measure.map f μ.toFinite = (Measure.map f μ).toFinite := by
  classical
  haveI : IsFiniteMeasure (Measure.map f μ) := ⟨by
    rw [Measure.map_apply hf MeasurableSet.univ]
    simp⟩
  have htoFinite :
      μ.toFinite = ProbabilityTheory.cond μ Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux, if_pos (inferInstance : IsFiniteMeasure μ)]
  have hmap_toFinite :
      (Measure.map f μ).toFinite =
        ProbabilityTheory.cond (Measure.map f μ) Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux,
      if_pos (inferInstance : IsFiniteMeasure (Measure.map f μ))]
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [htoFinite, hmap_toFinite]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ (f ⁻¹' s)]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ (Measure.map f μ) s]
  have hmap_univ : (Measure.map f μ) Set.univ = μ Set.univ := by
    rw [Measure.map_apply hf MeasurableSet.univ]
    simp
  rw [hmap_univ]
  simp [Set.univ_inter, Measure.map_apply hf hs]

/-- Multiplying a finite measure by a positive finite scalar does not
change its probability normalization. -/
theorem smul_toFinite_eq_toFinite
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] [IsFiniteMeasure μ]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    (c • μ).toFinite = μ.toFinite := by
  classical
  haveI : IsFiniteMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr hctop)
      (measure_lt_top μ Set.univ)⟩
  have htoFinite :
      μ.toFinite = ProbabilityTheory.cond μ Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux, if_pos (inferInstance : IsFiniteMeasure μ)]
  have hsmul_toFinite :
      (c • μ).toFinite = ProbabilityTheory.cond (c • μ) Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux,
      if_pos (inferInstance : IsFiniteMeasure (c • μ))]
  ext s hs
  rw [hsmul_toFinite, htoFinite]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ (c • μ) s]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ s]
  simp only [Set.univ_inter, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.mul_inv]
  · calc
      (c⁻¹ * (μ Set.univ)⁻¹) * (c * μ s)
          = (c⁻¹ * c) * ((μ Set.univ)⁻¹ * μ s) := by ac_rfl
      _ = (μ Set.univ)⁻¹ * μ s := by
        rw [ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  · exact Or.inl hc0
  · exact Or.inl hctop

/-- Probability-normalized surface measure is transported by a real linear
isometry between finite-dimensional real spaces, independently of the
normalization chosen for the ambient Haar measures. -/
theorem map_toFinite_toSphere_linearIsometryEquiv_of_map_eq_smul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial E] [Nontrivial F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    [SecondCountableTopology (Metric.sphere (0 : E) 1)]
    [SecondCountableTopology (Metric.sphere (0 : F) 1)]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure]
    [SFinite μ.toSphere] [IsFiniteMeasure μ.toSphere]
    [SFinite ν.toSphere] [IsFiniteMeasure ν.toSphere]
    (U : E ≃ₗᵢ[ℝ] F) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hμ : Measure.map U μ = c • ν) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        μ.toSphere.toFinite =
      ν.toSphere.toFinite := by
  let S : Metric.sphere (0 : E) 1 → Metric.sphere (0 : F) 1 :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S := by
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  have hμsphere0 : μ.toSphere Set.univ ≠ 0 := by
    have hne : μ.toSphere ≠ 0 := Measure.toSphere_ne_zero (μ := μ)
    exact fun hzero => hne (by
      ext s hs
      exact le_antisymm
        (by simpa [hzero] using measure_mono (μ := μ.toSphere) (Set.subset_univ s))
        bot_le)
  have hνsphere0 : ν.toSphere Set.univ ≠ 0 := by
    have hne : ν.toSphere ≠ 0 := Measure.toSphere_ne_zero (μ := ν)
    exact fun hzero => hne (by
      ext s hs
      exact le_antisymm
        (by simpa [hzero] using measure_mono (μ := ν.toSphere) (Set.subset_univ s))
        bot_le)
  have hmapSphere :
      Measure.map S μ.toSphere = c • ν.toSphere :=
    toSphere_map_linearIsometryEquiv_of_map_eq_smul
      (μ := μ) (ν := ν) U hμ
  have htoFiniteμ :
      μ.toSphere.toFinite = ProbabilityTheory.cond μ.toSphere Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux,
      if_pos (inferInstance : IsFiniteMeasure μ.toSphere)]
  have htoFiniteν :
      ν.toSphere.toFinite = ProbabilityTheory.cond ν.toSphere Set.univ := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux,
      if_pos (inferInstance : IsFiniteMeasure ν.toSphere)]
  ext t ht
  rw [Measure.map_apply hS_meas ht]
  rw [htoFiniteμ, htoFiniteν]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ.toSphere (S ⁻¹' t)]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ ν.toSphere t]
  simp only [Set.univ_inter]
  have ht_measure :
      μ.toSphere (S ⁻¹' t) = c * ν.toSphere t := by
    have h := congrArg (fun m : Measure (Metric.sphere (0 : F) 1) => m t) hmapSphere
    change (Measure.map S μ.toSphere) t = (c • ν.toSphere) t at h
    rw [Measure.map_apply hS_meas ht] at h
    simpa [Measure.smul_apply, smul_eq_mul] using h
  have huniv_measure :
      μ.toSphere Set.univ = c * ν.toSphere Set.univ := by
    have h := congrArg (fun m : Measure (Metric.sphere (0 : F) 1) => m Set.univ) hmapSphere
    change (Measure.map S μ.toSphere) Set.univ = (c • ν.toSphere) Set.univ at h
    rw [Measure.map_apply hS_meas MeasurableSet.univ] at h
    simpa [Measure.smul_apply, smul_eq_mul] using h
  rw [ht_measure, huniv_measure]
  rw [ENNReal.mul_inv]
  · calc
      (c⁻¹ * (ν.toSphere Set.univ)⁻¹) * (c * ν.toSphere t)
          = (c⁻¹ * c) * ((ν.toSphere Set.univ)⁻¹ * ν.toSphere t) := by ac_rfl
      _ = (ν.toSphere Set.univ)⁻¹ * ν.toSphere t := by
        rw [ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  · exact Or.inl hc0
  · exact Or.inl hctop

/-- The additive Haar/Lebesgue measure on the finite-dimensional real vector
space of complex sample matrices, with the Frobenius norm.  We use Mathlib's
canonical finite-dimensional basis choice only to name a Haar representative;
the probability-normalized surface law below is the canonical object used by
Appendix B. -/
def sampleHaarMeasure : Measure (SampleMatrix p q σ) :=
  (Module.finBasis ℝ (SampleMatrix p q σ)).addHaar

/-- The unnormalized surface measure on the Frobenius unit sphere, obtained by
Mathlib's `Measure.toSphere` construction from additive Haar measure. -/
def sampleSurfaceMeasure :
    Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
  (sampleHaarMeasure (p := p) (q := q) (σ := σ)).toSphere

omit [DecidableEq p] [DecidableEq q] in
/-- Conditional surface-measure invariance for sample matrices.

Once a concrete unitary action is shown to preserve `sampleHaarMeasure`, this
lemma immediately transports that invariance to the `toSphere` surface law. -/
theorem sampleSurfaceMeasure_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ)
    (hU :
      Measure.map U (sampleHaarMeasure (p := p) (q := q) (σ := σ)) =
        sampleHaarMeasure (p := p) (q := q) (σ := σ)) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        (sampleSurfaceMeasure (p := p) (q := q) (σ := σ)) =
      sampleSurfaceMeasure (p := p) (q := q) (σ := σ) := by
  haveI :
      (sampleHaarMeasure (p := p) (q := q) (σ := σ)).IsAddHaarMeasure := by
    unfold sampleHaarMeasure
    infer_instance
  unfold sampleSurfaceMeasure
  exact toSphere_map_linearIsometryEquiv_of_map_eq
    (μ := sampleHaarMeasure (p := p) (q := q) (σ := σ)) U hU

omit [DecidableEq p] [DecidableEq q] in
/-- Real linear isometries preserve the concrete additive Haar measure on the
finite-dimensional sample-matrix space. -/
theorem sampleHaarMeasure_map_linearIsometryEquiv
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ) :
    Measure.map U (sampleHaarMeasure (p := p) (q := q) (σ := σ)) =
      sampleHaarMeasure (p := p) (q := q) (σ := σ) := by
  let μ : Measure (SampleMatrix p q σ) :=
    sampleHaarMeasure (p := p) (q := q) (σ := σ)
  haveI : μ.IsAddHaarMeasure := by
    unfold μ sampleHaarMeasure
    infer_instance
  obtain ⟨c, hcpos, hmap⟩ :=
    U.toLinearEquiv.toLinearMap.exists_map_addHaar_eq_smul_addHaar
      (μ := μ) (ν := μ) U.toLinearEquiv.surjective
  have hmap' : Measure.map U μ = c • μ := by
    simpa using hmap
  have hball_nonempty : (Metric.ball (0 : SampleMatrix p q σ) 1).Nonempty := ⟨0, by simp⟩
  have hball_ne_zero : μ (Metric.ball (0 : SampleMatrix p q σ) 1) ≠ 0 := by
    have hopen : IsOpen (Metric.ball (0 : SampleMatrix p q σ) 1) := Metric.isOpen_ball
    exact hopen.measure_ne_zero μ hball_nonempty
  have hball_lt_top : μ (Metric.ball (0 : SampleMatrix p q σ) 1) < ∞ := by
    exact lt_of_le_of_lt
      (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : SampleMatrix p q σ) 1).measure_lt_top)
  have hball_eq :
      μ (Metric.ball (0 : SampleMatrix p q σ) 1) =
        c * μ (Metric.ball (0 : SampleMatrix p q σ) 1) := by
    have hopen : IsOpen (Metric.ball (0 : SampleMatrix p q σ) 1) := Metric.isOpen_ball
    have hpre :
        U ⁻¹' (Metric.ball (0 : SampleMatrix p q σ) 1) =
          Metric.ball (0 : SampleMatrix p q σ) 1 := by
      ext x
      simp [Metric.mem_ball, dist_eq_norm]
    calc
      μ (Metric.ball (0 : SampleMatrix p q σ) 1) =
          Measure.map U μ (Metric.ball (0 : SampleMatrix p q σ) 1) := by
            rw [Measure.map_apply U.continuous.measurable hopen.measurableSet, hpre]
      _ = (c • μ) (Metric.ball (0 : SampleMatrix p q σ) 1) := by rw [hmap']
      _ = c * μ (Metric.ball (0 : SampleMatrix p q σ) 1) := by simp
  have hc_one : c = 1 := by
    apply (ENNReal.mul_right_inj hball_ne_zero hball_lt_top.ne).mp
    simpa [mul_comm] using hball_eq.symm
  rw [hmap', hc_one, one_smul]

instance instSFiniteSampleSurfaceMeasure :
    SFinite (sampleSurfaceMeasure (p := p) (q := q) (σ := σ)) := by
  unfold sampleSurfaceMeasure sampleHaarMeasure
  infer_instance

instance instNeZeroSampleSurfaceMeasure [Nonempty p] [Nonempty q] [Nonempty σ] :
    NeZero (sampleSurfaceMeasure (p := p) (q := q) (σ := σ)) := by
  refine ⟨?_⟩
  unfold sampleSurfaceMeasure sampleHaarMeasure
  exact Measure.toSphere_ne_zero
    (μ := ((Module.finBasis ℝ (SampleMatrix p q σ)).addHaar :
      Measure (SampleMatrix p q σ)))

/-- The probability-uniform surface measure on the Frobenius unit sphere. -/
def sampleSurfaceProbabilityMeasure :
    Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
  (sampleSurfaceMeasure (p := p) (q := q) (σ := σ)).toFinite

omit [DecidableEq p] [DecidableEq q] in
/-- The unnormalized surface measure has finite total mass in the nondegenerate
finite-dimensional sample-matrix space. -/
theorem sampleSurfaceMeasure_lt_top_univ
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    sampleSurfaceMeasure (p := p) (q := q) (σ := σ) Set.univ < ∞ := by
  haveI :
      (sampleHaarMeasure (p := p) (q := q) (σ := σ)).IsAddHaarMeasure := by
    unfold sampleHaarMeasure
    infer_instance
  have hball_lt_top :
      sampleHaarMeasure (p := p) (q := q) (σ := σ)
          (Metric.ball (0 : SampleMatrix p q σ) 1) < ∞ := by
    refine lt_of_le_of_lt
      (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : SampleMatrix p q σ) 1).measure_lt_top)
  unfold sampleSurfaceMeasure
  rw [Measure.toSphere_apply_univ]
  exact ENNReal.mul_lt_top (by simp) hball_lt_top

omit [DecidableEq p] [DecidableEq q] in
/-- The probability-uniform surface measure on the Frobenius sphere is
invariant under any real linear isometry preserving the ambient Haar measure. -/
theorem sampleSurfaceProbabilityMeasure_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ)
    (hU :
      Measure.map U (sampleHaarMeasure (p := p) (q := q) (σ := σ)) =
        sampleHaarMeasure (p := p) (q := q) (σ := σ)) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
      sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ) := by
  let S : Metric.sphere (0 : SampleMatrix p q σ) 1 →
      Metric.sphere (0 : SampleMatrix p q σ) 1 :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S := by
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  let μ := sampleSurfaceMeasure (p := p) (q := q) (σ := σ)
  have hμ_map : Measure.map S μ = μ :=
    sampleSurfaceMeasure_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
      (p := p) (q := q) (σ := σ) U hU
  have hμ_fin : IsFiniteMeasure μ := ⟨by
    simpa [μ] using sampleSurfaceMeasure_lt_top_univ (p := p) (q := q) (σ := σ)⟩
  have htoFinite : μ.toFinite = μ[|Set.univ] := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux, if_pos hμ_fin]
  ext t ht
  rw [Measure.map_apply hS_meas ht]
  change μ.toFinite (S ⁻¹' t) = μ.toFinite t
  rw [htoFinite]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ]
  have hpre : μ (S ⁻¹' t) = μ t := by
    have h := congrArg (fun ν : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) => ν t) hμ_map
    simpa [Measure.map_apply hS_meas ht] using h
  simp [hpre]

/-- The ambient version of the probability-uniform surface measure. -/
def sampleSurfaceProbabilityMeasureAmbient : Measure (SampleMatrix p q σ) :=
  Measure.map Subtype.val
    (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient canonical surface law is invariant under the same linear
isometric action as the subtype surface law. -/
theorem sampleSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ)
    (hU :
      Measure.map U (sampleHaarMeasure (p := p) (q := q) (σ := σ)) =
        sampleHaarMeasure (p := p) (q := q) (σ := σ)) :
    Measure.map U
        (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) =
      sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ) := by
  let S : Metric.sphere (0 : SampleMatrix p q σ) 1 →
      Metric.sphere (0 : SampleMatrix p q σ) 1 :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S := by
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  unfold sampleSurfaceProbabilityMeasureAmbient
  calc
    Measure.map U
        (Measure.map Subtype.val
          (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))) =
      Measure.map (U ∘ Subtype.val)
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))
            (f := Subtype.val)
            (g := U)
            U.continuous.measurable
            continuous_subtype_val.measurable)
    _ =
      Measure.map (Subtype.val ∘ S)
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) := by
        rfl
    _ =
      Measure.map Subtype.val
        (Measure.map S
          (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))
            (f := S)
            (g := Subtype.val)
            continuous_subtype_val.measurable
            hS_meas).symm
    _ =
      Measure.map Subtype.val
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) := by
        rw [sampleSurfaceProbabilityMeasure_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
          (p := p) (q := q) (σ := σ) U hU]

omit [DecidableEq p] [DecidableEq q] in
/-- The canonical surface probability measure on the sample-matrix sphere is
invariant under every real linear isometry. -/
theorem sampleSurfaceProbabilityMeasure_map_linearIsometryEquiv
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
      sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ) := by
  exact sampleSurfaceProbabilityMeasure_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
    (p := p) (q := q) (σ := σ) U
    (sampleHaarMeasure_map_linearIsometryEquiv
      (p := p) (q := q) (σ := σ) U)

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient canonical surface law is invariant under every real linear
isometry of the sample-matrix space. -/
theorem sampleSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ) :
    Measure.map U
        (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) =
      sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ) := by
  exact sampleSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv_of_map_sampleHaarMeasure_eq
    (p := p) (q := q) (σ := σ) U
    (sampleHaarMeasure_map_linearIsometryEquiv
      (p := p) (q := q) (σ := σ) U)

omit [DecidableEq p] [DecidableEq q] in
/-- The normalized surface measure is a probability measure in every
nondegenerate sample-matrix space. -/
theorem sampleSurfaceProbabilityMeasure_isProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    IsProbabilityMeasure
      (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) := by
  unfold sampleSurfaceProbabilityMeasure
  infer_instance

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient normalized surface law is a probability measure. -/
theorem sampleSurfaceProbabilityMeasureAmbient_isProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    IsProbabilityMeasure
      (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) := by
  unfold sampleSurfaceProbabilityMeasureAmbient
  haveI :
      IsProbabilityMeasure
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) :=
    sampleSurfaceProbabilityMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  exact Measure.isProbabilityMeasure_map
    continuous_subtype_val.measurable.aemeasurable

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient normalized surface law is supported on the Frobenius unit
sphere. -/
theorem sampleSurfaceProbabilityMeasureAmbient_sphere
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)
        (Metric.sphere (0 : SampleMatrix p q σ) 1) = 1 := by
  haveI :
      IsProbabilityMeasure
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) :=
    sampleSurfaceProbabilityMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  unfold sampleSurfaceProbabilityMeasureAmbient
  rw [Measure.map_apply]
  · simp
  · exact continuous_subtype_val.measurable
  · exact Metric.isClosed_sphere.measurableSet

/-! ## Real `Fin n` sphere surface law

This is the standalone real-sphere model for the geometric core:
`S^{n-1}` is represented as `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`,
with surface measure obtained from Mathlib's `Measure.toSphere` construction.
-/

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The finite-dimensional real Euclidean space used for the canonical
`S^{n-1}` model. -/
abbrev FinRealEuclideanSpace (n : ℕ) :=
  EuclideanSpace ℝ (Fin n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The unit sphere in `ℝ^n`, represented as a subtype of
`EuclideanSpace ℝ (Fin n)`. -/
abbrev FinRealSphere (n : ℕ) :=
  Metric.sphere (0 : FinRealEuclideanSpace n) 1

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The canonical north pole of the concrete real sphere. -/
noncomputable def finRealSphereNorthPole (n : ℕ) [NeZero n] :
    FinRealSphere n :=
  ⟨EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ (1 : ℝ), by
    change
      dist
          (EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ (1 : ℝ) :
            FinRealEuclideanSpace n) 0 = 1
    rw [dist_eq_norm, sub_zero]
    simp⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Additive Haar/Lebesgue measure on `ℝ^n`, in Mathlib's canonical
finite-dimensional normalization. -/
def finRealHaarMeasure (n : ℕ) :
    Measure (FinRealEuclideanSpace n) :=
  (Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The unnormalised surface measure on `S^{n-1}`, obtained from ambient
Lebesgue/Haar measure by `Measure.toSphere`. -/
def finRealSurfaceMeasure (n : ℕ) :
    Measure (FinRealSphere n) :=
  (finRealHaarMeasure n).toSphere

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
instance instSFiniteFinRealSurfaceMeasure (n : ℕ) :
    SFinite (finRealSurfaceMeasure n) := by
  unfold finRealSurfaceMeasure finRealHaarMeasure
  infer_instance

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
instance instNeZeroFinRealSurfaceMeasure (n : ℕ) [NeZero n] :
    NeZero (finRealSurfaceMeasure n) := by
  refine ⟨?_⟩
  unfold finRealSurfaceMeasure finRealHaarMeasure
  exact Measure.toSphere_ne_zero
    (μ := ((Module.finBasis ℝ (FinRealEuclideanSpace n)).addHaar :
      Measure (FinRealEuclideanSpace n)))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The normalized surface probability law on `S^{n-1}`. -/
def finRealSurfaceProbabilityMeasure (n : ℕ) :
    Measure (FinRealSphere n) :=
  (finRealSurfaceMeasure n).toFinite

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The normalized surface law on `S^{n-1}` is a probability measure for
`n ≥ 1`. -/
theorem finRealSurfaceProbabilityMeasure_isProbabilityMeasure
    (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) := by
  unfold finRealSurfaceProbabilityMeasure
  infer_instance

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The ambient version of the normalized surface law on `S^{n-1}`. -/
def finRealSurfaceProbabilityMeasureAmbient (n : ℕ) :
    Measure (FinRealEuclideanSpace n) :=
  Measure.map
    ((↑) : FinRealSphere n → FinRealEuclideanSpace n)
    (finRealSurfaceProbabilityMeasure n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Transport from the sphere subtype to the ambient real Euclidean space. -/
theorem finRealSurfaceProbabilityMeasure_transport_to_ambient (n : ℕ) :
    Measure.map
        ((↑) : FinRealSphere n → FinRealEuclideanSpace n)
        (finRealSurfaceProbabilityMeasure n) =
      finRealSurfaceProbabilityMeasureAmbient n := by
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The ambient real-sphere law is a probability measure. -/
theorem finRealSurfaceProbabilityMeasureAmbient_isProbabilityMeasure
    (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (finRealSurfaceProbabilityMeasureAmbient n) := by
  unfold finRealSurfaceProbabilityMeasureAmbient
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  exact Measure.isProbabilityMeasure_map
    continuous_subtype_val.measurable.aemeasurable

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The ambient real-sphere law is supported on the unit sphere. -/
theorem finRealSurfaceProbabilityMeasureAmbient_sphere
    (n : ℕ) [NeZero n] :
    finRealSurfaceProbabilityMeasureAmbient n
        (Metric.sphere (0 : FinRealEuclideanSpace n) 1) = 1 := by
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  unfold finRealSurfaceProbabilityMeasureAmbient FinRealSphere
  rw [Measure.map_apply]
  · simp
  · exact continuous_subtype_val.measurable
  · exact Metric.isClosed_sphere.measurableSet

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Real linear isometries preserve the concrete additive Haar measure on
`ℝ^n`. -/
theorem finRealHaarMeasure_map_linearIsometryEquiv
    (n : ℕ) [NeZero n]
    (U : FinRealEuclideanSpace n ≃ₗᵢ[ℝ] FinRealEuclideanSpace n) :
    Measure.map U (finRealHaarMeasure n) = finRealHaarMeasure n := by
  let μ : Measure (FinRealEuclideanSpace n) := finRealHaarMeasure n
  haveI : μ.IsAddHaarMeasure := by
    unfold μ finRealHaarMeasure
    infer_instance
  obtain ⟨c, _hcpos, hmap⟩ :=
    U.toLinearEquiv.toLinearMap.exists_map_addHaar_eq_smul_addHaar
      (μ := μ) (ν := μ) U.toLinearEquiv.surjective
  have hmap' : Measure.map U μ = c • μ := by
    simpa using hmap
  have hball_nonempty : (Metric.ball (0 : FinRealEuclideanSpace n) 1).Nonempty :=
    ⟨0, by simp⟩
  have hball_ne_zero : μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ 0 := by
    have hopen : IsOpen (Metric.ball (0 : FinRealEuclideanSpace n) 1) := Metric.isOpen_ball
    exact hopen.measure_ne_zero μ hball_nonempty
  have hball_lt_top : μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) < ∞ := by
    exact lt_of_le_of_lt
      (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : FinRealEuclideanSpace n) 1).measure_lt_top)
  have hball_eq :
      μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) =
        c * μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    have hopen : IsOpen (Metric.ball (0 : FinRealEuclideanSpace n) 1) := Metric.isOpen_ball
    have hpre :
        U ⁻¹' (Metric.ball (0 : FinRealEuclideanSpace n) 1) =
          Metric.ball (0 : FinRealEuclideanSpace n) 1 := by
      ext x
      simp [Metric.mem_ball, dist_eq_norm]
    calc
      μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) =
          Measure.map U μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
            rw [Measure.map_apply U.continuous.measurable hopen.measurableSet, hpre]
      _ = (c • μ) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by rw [hmap']
      _ = c * μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by simp
  have hc_one : c = 1 := by
    apply (ENNReal.mul_right_inj hball_ne_zero hball_lt_top.ne).mp
    simpa [mul_comm] using hball_eq.symm
  rw [hmap', hc_one, one_smul]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The `Fin n` real surface probability law is invariant under every real
linear isometry of the ambient Euclidean space. -/
theorem finRealSurfaceProbabilityMeasure_map_linearIsometryEquiv
    (n : ℕ) [NeZero n]
    (U : FinRealEuclideanSpace n ≃ₗᵢ[ℝ] FinRealEuclideanSpace n) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        (finRealSurfaceProbabilityMeasure n) =
      finRealSurfaceProbabilityMeasure n := by
  let S : FinRealSphere n → FinRealSphere n :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S :=
    U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  let μ := finRealSurfaceMeasure n
  have hμ_map : Measure.map S μ = μ := by
    haveI : (finRealHaarMeasure n).IsAddHaarMeasure := by
      unfold finRealHaarMeasure
      infer_instance
    unfold μ finRealSurfaceMeasure
    exact toSphere_map_linearIsometryEquiv_of_map_eq
      (μ := finRealHaarMeasure n) U
      (finRealHaarMeasure_map_linearIsometryEquiv n U)
  have hμ_fin : IsFiniteMeasure μ := by
    unfold μ finRealSurfaceMeasure finRealHaarMeasure
    infer_instance
  have htoFinite : μ.toFinite = μ[|Set.univ] := by
    unfold Measure.toFinite
    rw [Measure.toFiniteAux, if_pos hμ_fin]
  ext t ht
  rw [Measure.map_apply hS_meas ht]
  change μ.toFinite (S ⁻¹' t) = μ.toFinite t
  rw [htoFinite]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ]
  rw [ProbabilityTheory.cond_apply MeasurableSet.univ μ]
  have hpre : μ (S ⁻¹' t) = μ t := by
    have h := congrArg (fun ν : Measure (FinRealSphere n) => ν t) hμ_map
    simpa [Measure.map_apply hS_meas ht] using h
  simp [hpre]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The ambient `Fin n` real surface law is invariant under every real linear
isometry of `ℝ^n`. -/
theorem finRealSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv
    (n : ℕ) [NeZero n]
    (U : FinRealEuclideanSpace n ≃ₗᵢ[ℝ] FinRealEuclideanSpace n) :
    Measure.map U (finRealSurfaceProbabilityMeasureAmbient n) =
      finRealSurfaceProbabilityMeasureAmbient n := by
  let S : FinRealSphere n → FinRealSphere n :=
    Subtype.map U (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S :=
    U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  unfold finRealSurfaceProbabilityMeasureAmbient
  calc
    Measure.map U
        (Measure.map Subtype.val (finRealSurfaceProbabilityMeasure n)) =
      Measure.map (U ∘ Subtype.val) (finRealSurfaceProbabilityMeasure n) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := finRealSurfaceProbabilityMeasure n)
            (f := Subtype.val)
            (g := U)
            U.continuous.measurable
            continuous_subtype_val.measurable)
    _ =
      Measure.map (Subtype.val ∘ S) (finRealSurfaceProbabilityMeasure n) := by
        rfl
    _ =
      Measure.map Subtype.val
        (Measure.map S (finRealSurfaceProbabilityMeasure n)) := by
        simpa [Function.comp] using
          (Measure.map_map
            (μ := finRealSurfaceProbabilityMeasure n)
            (f := S)
            (g := Subtype.val)
            continuous_subtype_val.measurable
            hS_meas).symm
    _ =
      Measure.map Subtype.val (finRealSurfaceProbabilityMeasure n) := by
        rw [finRealSurfaceProbabilityMeasure_map_linearIsometryEquiv n U]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The intrinsic orthogonal group of `ℝ^n`, represented as real linear
isometric automorphisms.  This is the coordinate-free `O(n)` action used by
the real spherical isoperimetric layer. -/
abbrev FinRealOrthogonalGroup (n : ℕ) :=
  FinRealEuclideanSpace n ≃ₗᵢ[ℝ] FinRealEuclideanSpace n

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The action of an orthogonal transformation on the real unit sphere. -/
def finRealOrthogonalSphereMap
    (n : ℕ) (U : FinRealOrthogonalGroup n) :
    FinRealSphere n → FinRealSphere n :=
  Subtype.map U (fun _ hx => by simpa using hx)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal invariance of the normalized real surface probability law on
`S^{n-1}`. -/
theorem finRealSurfaceProbabilityMeasure_map_orthogonal
    (n : ℕ) [NeZero n]
    (U : FinRealOrthogonalGroup n) :
    Measure.map (finRealOrthogonalSphereMap n U)
        (finRealSurfaceProbabilityMeasure n) =
      finRealSurfaceProbabilityMeasure n := by
  simpa [finRealOrthogonalSphereMap, FinRealOrthogonalGroup] using
    finRealSurfaceProbabilityMeasure_map_linearIsometryEquiv n U

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal invariance of the ambient real surface probability law. -/
theorem finRealSurfaceProbabilityMeasureAmbient_map_orthogonal
    (n : ℕ) [NeZero n]
    (U : FinRealOrthogonalGroup n) :
    Measure.map U (finRealSurfaceProbabilityMeasureAmbient n) =
      finRealSurfaceProbabilityMeasureAmbient n := by
  simpa [FinRealOrthogonalGroup] using
    finRealSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv n U

/-! ## Geodesic distance and Euclidean thickenings on the real sphere -/

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Scalar chord-arc comparison on the unit sphere, written in terms of the
chord length `c ∈ [0, 2]` and the spherical arc length
`2 * arcsin (c / 2)`. -/
theorem real_chord_le_two_mul_arcsin_half
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    c ≤ 2 * Real.arcsin (c / 2) := by
  have harg0 : 0 ≤ c / 2 := by positivity
  have harg1 : c / 2 ≤ 1 := by linarith
  have hargm1 : -1 ≤ c / 2 := by linarith
  have hy0 : 0 ≤ Real.arcsin (c / 2) :=
    Real.arcsin_nonneg.mpr harg0
  have hsin :
      Real.sin (Real.arcsin (c / 2)) = c / 2 :=
    Real.sin_arcsin hargm1 harg1
  have hhalf : c / 2 ≤ Real.arcsin (c / 2) := by
    simpa [hsin] using Real.sin_le hy0
  linarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The spherical geodesic distance on `S^{n-1}`, expressed through the
ambient Euclidean chord length.  For unit vectors this is the usual great
circle distance. -/
noncomputable def finRealSphereGeodesicDistance
    (n : ℕ) (x y : FinRealSphere n) : ℝ :=
  2 * Real.arcsin (dist x y / 2)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The chord distance between two points of the unit sphere is at most `2`. -/
theorem finRealSphere_dist_le_two
    (n : ℕ) (x y : FinRealSphere n) :
    dist x y ≤ 2 := by
  have hx : dist (x : FinRealEuclideanSpace n) 0 = 1 := by
    exact x.2
  have hy : dist (y : FinRealEuclideanSpace n) 0 = 1 := by
    exact y.2
  have htri :
      dist (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ≤
        dist (x : FinRealEuclideanSpace n) 0 +
          dist 0 (y : FinRealEuclideanSpace n) :=
    dist_triangle _ _ _
  have htri' :
      dist (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ≤
        2 := by
    calc
      dist (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ≤
          dist (x : FinRealEuclideanSpace n) 0 +
            dist 0 (y : FinRealEuclideanSpace n) := htri
      _ = 2 := by
        rw [hx, dist_comm, hy]
        norm_num
  simpa using htri'

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Chord-arc comparison on the real unit sphere: Euclidean/chord distance is
bounded by spherical geodesic distance. -/
theorem finRealSphere_dist_le_geodesicDistance
    (n : ℕ) (x y : FinRealSphere n) :
    dist x y ≤ finRealSphereGeodesicDistance n x y := by
  exact real_chord_le_two_mul_arcsin_half
    (dist_nonneg)
    (finRealSphere_dist_le_two n x y)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open thickening with respect to the spherical geodesic distance. -/
noncomputable def finRealSphereGeodesicThickening
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) :
    Set (FinRealSphere n) :=
  {x | ∃ y ∈ A, finRealSphereGeodesicDistance n x y < r}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Geodesic thickenings are open, since they are unions of open geodesic
caps. -/
theorem isOpen_finRealSphereGeodesicThickening
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) :
    IsOpen (finRealSphereGeodesicThickening n r A) := by
  rw [show finRealSphereGeodesicThickening n r A =
      ⋃ y ∈ A, {x : FinRealSphere n | finRealSphereGeodesicDistance n x y < r} by
    ext x
    simp [finRealSphereGeodesicThickening]]
  exact isOpen_iUnion fun y =>
    isOpen_iUnion fun _ => by
      have hcont :
          Continuous (fun x : FinRealSphere n =>
            finRealSphereGeodesicDistance n x y) := by
        unfold finRealSphereGeodesicDistance
        fun_prop
      exact isOpen_Iio.preimage hcont

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Geodesic thickenings are measurable. -/
theorem measurableSet_finRealSphereGeodesicThickening
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) :
    MeasurableSet (finRealSphereGeodesicThickening n r A) :=
  (isOpen_finRealSphereGeodesicThickening n r A).measurableSet

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal maps preserve the ambient chord distance on the concrete real
sphere. -/
theorem finRealOrthogonalSphereMap_dist
    (n : ℕ) (U : FinRealOrthogonalGroup n) (x y : FinRealSphere n) :
    dist (finRealOrthogonalSphereMap n U x)
        (finRealOrthogonalSphereMap n U y) =
      dist x y := by
  change
    dist (U (x : FinRealEuclideanSpace n)) (U (y : FinRealEuclideanSpace n)) =
      dist (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)
  exact LinearIsometryEquiv.dist_map U
    (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal maps preserve the geodesic distance used by the real-sphere
isoperimetric layer. -/
theorem finRealOrthogonalSphereMap_geodesicDistance
    (n : ℕ) (U : FinRealOrthogonalGroup n) (x y : FinRealSphere n) :
    finRealSphereGeodesicDistance n
        (finRealOrthogonalSphereMap n U x)
        (finRealOrthogonalSphereMap n U y) =
      finRealSphereGeodesicDistance n x y := by
  unfold finRealSphereGeodesicDistance
  rw [finRealOrthogonalSphereMap_dist]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Orthogonal maps transport geodesic thickenings to geodesic thickenings of
the transported set. -/
theorem finRealOrthogonalSphereMap_image_geodesicThickening
    (n : ℕ) (U : FinRealOrthogonalGroup n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealOrthogonalSphereMap n U ''
        finRealSphereGeodesicThickening n r A =
      finRealSphereGeodesicThickening n r
        (finRealOrthogonalSphereMap n U '' A) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hyA, hdist⟩
    refine ⟨finRealOrthogonalSphereMap n U y, ⟨y, hyA, rfl⟩, ?_⟩
    rwa [finRealOrthogonalSphereMap_geodesicDistance]
  · intro hz
    rcases hz with ⟨y, hy, hdist⟩
    rcases hy with ⟨a, haA, rfl⟩
    refine ⟨finRealOrthogonalSphereMap n U.symm z, ?_, ?_⟩
    · refine ⟨a, haA, ?_⟩
      have hdist_eq :
          finRealSphereGeodesicDistance n
              (finRealOrthogonalSphereMap n U.symm z) a =
            finRealSphereGeodesicDistance n z
              (finRealOrthogonalSphereMap n U a) := by
        have hcompz :
            finRealOrthogonalSphereMap n U
                (finRealOrthogonalSphereMap n U.symm z) = z := by
          apply Subtype.ext
          simp [finRealOrthogonalSphereMap]
        have hgeo :=
          finRealOrthogonalSphereMap_geodesicDistance n U
            (finRealOrthogonalSphereMap n U.symm z) a
        rw [hcompz] at hgeo
        exact hgeo.symm
      rwa [hdist_eq]
    · apply Subtype.ext
      simp [finRealOrthogonalSphereMap]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Preimage form of orthogonal transport for geodesic thickenings. -/
theorem finRealOrthogonalSphereMap_preimage_geodesicThickening_image
    (n : ℕ) (U : FinRealOrthogonalGroup n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealOrthogonalSphereMap n U) ⁻¹'
        finRealSphereGeodesicThickening n r
          (finRealOrthogonalSphereMap n U '' A) =
      finRealSphereGeodesicThickening n r A := by
  ext x
  constructor
  · intro hx
    have himg :
        finRealOrthogonalSphereMap n U x ∈
          finRealOrthogonalSphereMap n U ''
            finRealSphereGeodesicThickening n r A := by
      rw [finRealOrthogonalSphereMap_image_geodesicThickening]
      exact hx
    rcases himg with ⟨z, hz, hzx⟩
    have hxz : x = z := by
      apply Subtype.ext
      have hval :
          U (z : FinRealEuclideanSpace n) =
            U (x : FinRealEuclideanSpace n) :=
        congrArg Subtype.val hzx
      exact (U.injective hval).symm
    simpa [hxz] using hz
  · intro hx
    have himg :
        finRealOrthogonalSphereMap n U x ∈
          finRealOrthogonalSphereMap n U ''
            finRealSphereGeodesicThickening n r A :=
      ⟨x, hx, rfl⟩
    rw [finRealOrthogonalSphereMap_image_geodesicThickening] at himg
    exact himg

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The geodesic-neighbourhood complement objective is invariant under any
orthogonal image of the competitor. -/
theorem finRealSurfaceProbabilityMeasure_orthogonal_image_neighbourhoodComplement_real
    {n : ℕ} [NeZero n] (U : FinRealOrthogonalGroup n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealOrthogonalSphereMap n U '' A))ᶜ) =
      (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r A)ᶜ) := by
  let T :=
    finRealSphereGeodesicThickening n r
      (finRealOrthogonalSphereMap n U '' A)
  have hT : MeasurableSet T :=
    measurableSet_finRealSphereGeodesicThickening n r
      (finRealOrthogonalSphereMap n U '' A)
  have hS_meas : Measurable (finRealOrthogonalSphereMap n U) := by
    dsimp [finRealOrthogonalSphereMap]
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  calc
    (finRealSurfaceProbabilityMeasure n).real Tᶜ =
        (Measure.map (finRealOrthogonalSphereMap n U)
          (finRealSurfaceProbabilityMeasure n)).real Tᶜ := by
          rw [finRealSurfaceProbabilityMeasure_map_orthogonal n U]
    _ =
        (finRealSurfaceProbabilityMeasure n).real
          ((finRealOrthogonalSphereMap n U) ⁻¹' Tᶜ) := by
          rw [map_measureReal_apply hS_meas hT.compl]
    _ =
        (finRealSurfaceProbabilityMeasure n).real
          (((finRealOrthogonalSphereMap n U) ⁻¹' T)ᶜ) := by
          rw [Set.preimage_compl]
    _ =
        (finRealSurfaceProbabilityMeasure n).real
          ((finRealSphereGeodesicThickening n r A)ᶜ) := by
          rw [finRealOrthogonalSphereMap_preimage_geodesicThickening_image]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Geodesic thickening is contained in Euclidean/chord thickening with the
same radius.  This is the direction needed to pass from a geodesic
isoperimetric theorem to the Frobenius neighbourhoods used downstream. -/
theorem finRealSphereGeodesicThickening_subset_metricThickening
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) :
    finRealSphereGeodesicThickening n r A ⊆ Metric.thickening r A := by
  intro x hx
  rcases hx with ⟨y, hyA, hgeo⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨y, hyA, ?_⟩
  exact lt_of_le_of_lt (finRealSphere_dist_le_geodesicDistance n x y) hgeo

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- After transporting the sphere to the ambient Euclidean space, geodesic
thickening still lands inside the ambient Euclidean thickening of the
transported set. -/
theorem finRealSphereGeodesicThickening_image_subset_ambientThickening_image
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) :
    Subtype.val '' finRealSphereGeodesicThickening n r A ⊆
      Metric.thickening r (((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' A) := by
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  rcases hu with ⟨v, hvA, hgeo⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨(v : FinRealEuclideanSpace n), ⟨v, hvA, rfl⟩, ?_⟩
  exact lt_of_le_of_lt (finRealSphere_dist_le_geodesicDistance n u v) hgeo

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Complement comparison in measure form: under the ambient push-forward
surface law, the complement of an ambient Euclidean thickening has measure at
most the complement of the corresponding geodesic thickening on the sphere. -/
theorem finRealSurfaceProbabilityMeasureAmbient_compl_ambientThickening_image_le_geodesic
    (n : ℕ) (r : ℝ) (A : Set (FinRealSphere n)) :
    (finRealSurfaceProbabilityMeasureAmbient n).real
        ((Metric.thickening r
          (((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' A))ᶜ) ≤
      (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r A)ᶜ) := by
  have hpre :
      ((↑) : FinRealSphere n → FinRealEuclideanSpace n) ⁻¹'
          ((Metric.thickening r
            (((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' A))ᶜ) ⊆
        (finRealSphereGeodesicThickening n r A)ᶜ := by
    intro x hx hgeo
    exact hx
      (finRealSphereGeodesicThickening_image_subset_ambientThickening_image
        n r A ⟨x, hgeo, rfl⟩)
  unfold finRealSurfaceProbabilityMeasureAmbient
  rw [map_measureReal_apply
    continuous_subtype_val.measurable
    Metric.isOpen_thickening.measurableSet.compl]
  haveI : IsFiniteMeasure (finRealSurfaceProbabilityMeasure n) := by
    unfold finRealSurfaceProbabilityMeasure
    infer_instance
  exact measureReal_mono hpre
    (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasure n)
      ((finRealSphereGeodesicThickening n r A)ᶜ)).ne)

/-! ## Halfspaces and caps on the real sphere -/

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Linear coordinate on the real sphere in the direction `e`. -/
noncomputable def finRealSphereInnerCoordinate
    (n : ℕ) (e : FinRealEuclideanSpace n) (x : FinRealSphere n) : ℝ :=
  inner ℝ e (x : FinRealEuclideanSpace n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The coordinate map `x ↦ ⟪e,x⟫` is continuous on the sphere. -/
theorem continuous_finRealSphereInnerCoordinate
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    Continuous (finRealSphereInnerCoordinate n e) := by
  simpa [finRealSphereInnerCoordinate] using
    (continuous_const.inner continuous_subtype_val :
      Continuous fun x : FinRealSphere n =>
        inner ℝ e (x : FinRealEuclideanSpace n))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Ambient closed halfspace with normal `e` and threshold `t`. -/
noncomputable def finRealAmbientClosedHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    Set (FinRealEuclideanSpace n) :=
  {x | t ≤ inner ℝ e x}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Ambient open halfspace with normal `e` and threshold `t`. -/
noncomputable def finRealAmbientOpenHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    Set (FinRealEuclideanSpace n) :=
  {x | t < inner ℝ e x}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed halfspace cut out on the real unit sphere. -/
noncomputable def finRealSphereClosedHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    Set (FinRealSphere n) :=
  {x | t ≤ finRealSphereInnerCoordinate n e x}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open halfspace cut out on the real unit sphere. -/
noncomputable def finRealSphereOpenHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    Set (FinRealSphere n) :=
  {x | t < finRealSphereInnerCoordinate n e x}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed hemisphere with pole/normal `e`. -/
noncomputable def finRealSphereClosedHemisphere
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    Set (FinRealSphere n) :=
  finRealSphereClosedHalfspace n e 0

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open hemisphere with pole/normal `e`. -/
noncomputable def finRealSphereOpenHemisphere
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    Set (FinRealSphere n) :=
  finRealSphereOpenHalfspace n e 0

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed spherical cap with centre `c` and height threshold `t`.

For a unit centre `c`, this is `{x ∈ S^{n-1} | t ≤ ⟪c,x⟫}`. -/
noncomputable def finRealSphereClosedCap
    (n : ℕ) (c : FinRealSphere n) (t : ℝ) :
    Set (FinRealSphere n) :=
  finRealSphereClosedHalfspace n (c : FinRealEuclideanSpace n) t

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open spherical cap with centre `c` and height threshold `t`. -/
noncomputable def finRealSphereOpenCap
    (n : ℕ) (c : FinRealSphere n) (t : ℝ) :
    Set (FinRealSphere n) :=
  finRealSphereOpenHalfspace n (c : FinRealEuclideanSpace n) t

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed angular cap with centre `c` and angular radius `θ`, written as a
halfspace threshold `cos θ`. -/
noncomputable def finRealSphereClosedAngularCap
    (n : ℕ) (c : FinRealSphere n) (θ : ℝ) :
    Set (FinRealSphere n) :=
  finRealSphereClosedCap n c (Real.cos θ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open angular cap with centre `c` and angular radius `θ`, written as a
halfspace threshold `cos θ`. -/
noncomputable def finRealSphereOpenAngularCap
    (n : ℕ) (c : FinRealSphere n) (θ : ℝ) :
    Set (FinRealSphere n) :=
  finRealSphereOpenCap n c (Real.cos θ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open geodesic cap centred at `c` with radius `r`. -/
noncomputable def finRealSphereOpenGeodesicCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    Set (FinRealSphere n) :=
  {x | finRealSphereGeodesicDistance n x c < r}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed geodesic cap centred at `c` with radius `r`. -/
noncomputable def finRealSphereClosedGeodesicCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    Set (FinRealSphere n) :=
  {x | finRealSphereGeodesicDistance n x c ≤ r}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open Euclidean/chord cap centred at `c` with chord radius `r`. -/
noncomputable def finRealSphereOpenEuclideanCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    Set (FinRealSphere n) :=
  Metric.ball c r

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed Euclidean/chord cap centred at `c` with chord radius `r`. -/
noncomputable def finRealSphereClosedEuclideanCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    Set (FinRealSphere n) :=
  Metric.closedBall c r

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Chord-length squared on the real unit sphere in terms of the ambient inner
product.  This is the elementary cap-geometry identity behind the conversion
between Euclidean/chord balls and halfspace caps. -/
theorem finRealSphere_dist_sq_eq_two_sub_two_inner
    (n : ℕ) (x y : FinRealSphere n) :
    dist x y ^ 2 =
      2 - 2 *
        inner ℝ (x : FinRealEuclideanSpace n)
          (y : FinRealEuclideanSpace n) := by
  have hxnorm : ‖(x : FinRealEuclideanSpace n)‖ = 1 := by
    have hx : dist (x : FinRealEuclideanSpace n) 0 = 1 := x.2
    rw [dist_eq_norm, sub_zero] at hx
    exact hx
  have hynorm : ‖(y : FinRealEuclideanSpace n)‖ = 1 := by
    have hy : dist (y : FinRealEuclideanSpace n) 0 = 1 := y.2
    rw [dist_eq_norm, sub_zero] at hy
    exact hy
  calc
    dist x y ^ 2 =
        ‖(x : FinRealEuclideanSpace n) -
          (y : FinRealEuclideanSpace n)‖ ^ 2 := by
      change
        dist (x : FinRealEuclideanSpace n) (y : FinRealEuclideanSpace n) ^ 2 =
          ‖(x : FinRealEuclideanSpace n) -
            (y : FinRealEuclideanSpace n)‖ ^ 2
      rw [dist_eq_norm]
    _ =
        ‖(x : FinRealEuclideanSpace n)‖ ^ 2 -
          2 *
            inner ℝ (x : FinRealEuclideanSpace n)
              (y : FinRealEuclideanSpace n) +
          ‖(y : FinRealEuclideanSpace n)‖ ^ 2 := by
      rw [norm_sub_sq_real]
    _ =
        2 - 2 *
          inner ℝ (x : FinRealEuclideanSpace n)
            (y : FinRealEuclideanSpace n) := by
      rw [hxnorm, hynorm]
      ring

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- An open Euclidean/chord cap on the real unit sphere is exactly the open
halfspace cap with threshold `1 - r^2 / 2`. -/
theorem finRealSphereOpenEuclideanCap_eq_openCap_radius
    (n : ℕ) (c : FinRealSphere n) {r : ℝ} (hr : 0 ≤ r) :
    finRealSphereOpenEuclideanCap n c r =
      finRealSphereOpenCap n c (1 - r ^ 2 / 2) := by
  ext x
  constructor
  · intro hx
    have hdist : dist x c < r := by
      simpa [finRealSphereOpenEuclideanCap, Metric.mem_ball] using hx
    have hsq : dist x c ^ 2 < r ^ 2 := by
      rwa [sq_lt_sq₀ dist_nonneg hr]
    have hgeom := finRealSphere_dist_sq_eq_two_sub_two_inner n x c
    have hinner :
        1 - r ^ 2 / 2 <
          inner ℝ (c : FinRealEuclideanSpace n)
            (x : FinRealEuclideanSpace n) := by
      rw [hgeom] at hsq
      rw [real_inner_comm] at hsq
      linarith
    simpa [finRealSphereOpenCap, finRealSphereOpenHalfspace,
      finRealSphereInnerCoordinate] using hinner
  · intro hx
    have hinner :
        1 - r ^ 2 / 2 <
          inner ℝ (c : FinRealEuclideanSpace n)
            (x : FinRealEuclideanSpace n) := by
      simpa [finRealSphereOpenCap, finRealSphereOpenHalfspace,
        finRealSphereInnerCoordinate] using hx
    have hsq : dist x c ^ 2 < r ^ 2 := by
      have hgeom := finRealSphere_dist_sq_eq_two_sub_two_inner n x c
      rw [hgeom, real_inner_comm]
      linarith
    have hdist : dist x c < r := by
      rwa [sq_lt_sq₀ dist_nonneg hr] at hsq
    simpa [finRealSphereOpenEuclideanCap, Metric.mem_ball] using hdist

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A closed Euclidean/chord cap on the real unit sphere is exactly the closed
halfspace cap with threshold `1 - r^2 / 2`. -/
theorem finRealSphereClosedEuclideanCap_eq_closedCap_radius
    (n : ℕ) (c : FinRealSphere n) {r : ℝ} (hr : 0 ≤ r) :
    finRealSphereClosedEuclideanCap n c r =
      finRealSphereClosedCap n c (1 - r ^ 2 / 2) := by
  ext x
  constructor
  · intro hx
    have hdist : dist x c ≤ r := by
      simpa [finRealSphereClosedEuclideanCap, Metric.mem_closedBall] using hx
    have hsq : dist x c ^ 2 ≤ r ^ 2 := by
      rwa [sq_le_sq₀ dist_nonneg hr]
    have hgeom := finRealSphere_dist_sq_eq_two_sub_two_inner n x c
    have hinner :
        1 - r ^ 2 / 2 ≤
          inner ℝ (c : FinRealEuclideanSpace n)
            (x : FinRealEuclideanSpace n) := by
      rw [hgeom] at hsq
      rw [real_inner_comm] at hsq
      linarith
    simpa [finRealSphereClosedCap, finRealSphereClosedHalfspace,
      finRealSphereInnerCoordinate] using hinner
  · intro hx
    have hinner :
        1 - r ^ 2 / 2 ≤
          inner ℝ (c : FinRealEuclideanSpace n)
            (x : FinRealEuclideanSpace n) := by
      simpa [finRealSphereClosedCap, finRealSphereClosedHalfspace,
        finRealSphereInnerCoordinate] using hx
    have hsq : dist x c ^ 2 ≤ r ^ 2 := by
      have hgeom := finRealSphere_dist_sq_eq_two_sub_two_inner n x c
      rw [hgeom, real_inner_comm]
      linarith
    have hdist : dist x c ≤ r := by
      rwa [sq_le_sq₀ dist_nonneg hr] at hsq
    simpa [finRealSphereClosedEuclideanCap, Metric.mem_closedBall] using hdist

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Continuity of the geodesic distance from a fixed centre on the concrete
real sphere. -/
theorem continuous_finRealSphereGeodesicDistance_left
    (n : ℕ) (c : FinRealSphere n) :
    Continuous (fun x : FinRealSphere n =>
      finRealSphereGeodesicDistance n x c) := by
  unfold finRealSphereGeodesicDistance
  fun_prop

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Open geodesic caps are open in the subtype topology on the real sphere. -/
theorem isOpen_finRealSphereOpenGeodesicCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    IsOpen (finRealSphereOpenGeodesicCap n c r) := by
  have hcont := continuous_finRealSphereGeodesicDistance_left n c
  simpa [finRealSphereOpenGeodesicCap] using
    (isOpen_Iio.preimage hcont)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed geodesic caps are closed in the subtype topology on the real
sphere. -/
theorem isClosed_finRealSphereClosedGeodesicCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    IsClosed (finRealSphereClosedGeodesicCap n c r) := by
  have hcont := continuous_finRealSphereGeodesicDistance_left n c
  simpa [finRealSphereClosedGeodesicCap] using
    (isClosed_Iic.preimage hcont)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Measurability of open geodesic caps. -/
theorem measurableSet_finRealSphereOpenGeodesicCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    MeasurableSet (finRealSphereOpenGeodesicCap n c r) :=
  (isOpen_finRealSphereOpenGeodesicCap n c r).measurableSet

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Measurability of closed geodesic caps. -/
theorem measurableSet_finRealSphereClosedGeodesicCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    MeasurableSet (finRealSphereClosedGeodesicCap n c r) :=
  (isClosed_finRealSphereClosedGeodesicCap n c r).measurableSet

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem isClosed_finRealSphereClosedHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    IsClosed (finRealSphereClosedHalfspace n e t) := by
  have hcont := continuous_finRealSphereInnerCoordinate n e
  simpa [finRealSphereClosedHalfspace] using
    (isClosed_Ici.preimage hcont)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem isOpen_finRealSphereOpenHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    IsOpen (finRealSphereOpenHalfspace n e t) := by
  have hcont := continuous_finRealSphereInnerCoordinate n e
  simpa [finRealSphereOpenHalfspace] using
    (isOpen_Ioi.preimage hcont)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem measurableSet_finRealSphereClosedHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    MeasurableSet (finRealSphereClosedHalfspace n e t) :=
  (isClosed_finRealSphereClosedHalfspace n e t).measurableSet

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem measurableSet_finRealSphereOpenHalfspace
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    MeasurableSet (finRealSphereOpenHalfspace n e t) :=
  (isOpen_finRealSphereOpenHalfspace n e t).measurableSet

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem measurableSet_finRealSphereClosedHemisphere
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    MeasurableSet (finRealSphereClosedHemisphere n e) := by
  simpa [finRealSphereClosedHemisphere] using
    measurableSet_finRealSphereClosedHalfspace n e 0

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem measurableSet_finRealSphereOpenHemisphere
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    MeasurableSet (finRealSphereOpenHemisphere n e) := by
  simpa [finRealSphereOpenHemisphere] using
    measurableSet_finRealSphereOpenHalfspace n e 0

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem measurableSet_finRealSphereClosedCap
    (n : ℕ) (c : FinRealSphere n) (t : ℝ) :
    MeasurableSet (finRealSphereClosedCap n c t) := by
  simpa [finRealSphereClosedCap] using
    measurableSet_finRealSphereClosedHalfspace n
      (c : FinRealEuclideanSpace n) t

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
theorem measurableSet_finRealSphereOpenCap
    (n : ℕ) (c : FinRealSphere n) (t : ℝ) :
    MeasurableSet (finRealSphereOpenCap n c t) := by
  simpa [finRealSphereOpenCap] using
    measurableSet_finRealSphereOpenHalfspace n
      (c : FinRealEuclideanSpace n) t

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The law of the real coordinate `x ↦ ⟪e,x⟫` under normalized surface measure
on the finite-dimensional real sphere. -/
noncomputable def finRealSphereCoordinateLaw
    (n : ℕ) (e : FinRealEuclideanSpace n) : Measure ℝ :=
  Measure.map (finRealSphereInnerCoordinate n e)
    (finRealSurfaceProbabilityMeasure n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The coordinate law is a probability measure whenever the real sphere is
nonempty in positive dimension. -/
theorem finRealSphereCoordinateLaw_isProbabilityMeasure
    (n : ℕ) [NeZero n] (e : FinRealEuclideanSpace n) :
    IsProbabilityMeasure (finRealSphereCoordinateLaw n e) := by
  unfold finRealSphereCoordinateLaw
  haveI := finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  exact Measure.isProbabilityMeasure_map
    (continuous_finRealSphereInnerCoordinate n e).aemeasurable

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A closed spherical halfspace has measure equal to the upper tail of the
corresponding one-dimensional coordinate law. -/
theorem sphereClosedHalfspaceMeasure_coordinate_formula
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHalfspace n e t) =
      (finRealSphereCoordinateLaw n e).real (Set.Ici t) := by
  symm
  unfold finRealSphereCoordinateLaw finRealSphereClosedHalfspace
  rw [map_measureReal_apply
    (continuous_finRealSphereInnerCoordinate n e).measurable
    measurableSet_Ici]
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- An open spherical halfspace has measure equal to the strict upper tail of
the corresponding one-dimensional coordinate law. -/
theorem sphereOpenHalfspaceMeasure_coordinate_formula
    (n : ℕ) (e : FinRealEuclideanSpace n) (t : ℝ) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereOpenHalfspace n e t) =
      (finRealSphereCoordinateLaw n e).real (Set.Ioi t) := by
  symm
  unfold finRealSphereCoordinateLaw finRealSphereOpenHalfspace
  rw [map_measureReal_apply
    (continuous_finRealSphereInnerCoordinate n e).measurable
    measurableSet_Ioi]
  rfl

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Coordinate formula for the measure of a closed spherical cap.  This is the
cap version of `sphereClosedHalfspaceMeasure_coordinate_formula`. -/
theorem sphereCapMeasure_coordinate_formula
    (n : ℕ) (c : FinRealSphere n) (t : ℝ) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedCap n c t) =
      (finRealSphereCoordinateLaw n (c : FinRealEuclideanSpace n)).real
        (Set.Ici t) := by
  simpa [finRealSphereClosedCap] using
    sphereClosedHalfspaceMeasure_coordinate_formula n
      (c : FinRealEuclideanSpace n) t

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Coordinate formula for the measure of an open spherical cap. -/
theorem sphereOpenCapMeasure_coordinate_formula
    (n : ℕ) (c : FinRealSphere n) (t : ℝ) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereOpenCap n c t) =
      (finRealSphereCoordinateLaw n (c : FinRealEuclideanSpace n)).real
        (Set.Ioi t) := by
  simpa [finRealSphereOpenCap] using
    sphereOpenHalfspaceMeasure_coordinate_formula n
      (c : FinRealEuclideanSpace n) t

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Coordinate formula for the measure of an open Euclidean/chord cap. -/
theorem sphereOpenEuclideanCapMeasure_coordinate_formula
    (n : ℕ) (c : FinRealSphere n) {r : ℝ} (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereOpenEuclideanCap n c r) =
      (finRealSphereCoordinateLaw n (c : FinRealEuclideanSpace n)).real
        (Set.Ioi (1 - r ^ 2 / 2)) := by
  rw [finRealSphereOpenEuclideanCap_eq_openCap_radius n c hr]
  exact sphereOpenCapMeasure_coordinate_formula n c (1 - r ^ 2 / 2)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Coordinate formula for the measure of a closed Euclidean/chord cap. -/
theorem sphereClosedEuclideanCapMeasure_coordinate_formula
    (n : ℕ) (c : FinRealSphere n) {r : ℝ} (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedEuclideanCap n c r) =
      (finRealSphereCoordinateLaw n (c : FinRealEuclideanSpace n)).real
        (Set.Ici (1 - r ^ 2 / 2)) := by
  rw [finRealSphereClosedEuclideanCap_eq_closedCap_radius n c hr]
  exact sphereCapMeasure_coordinate_formula n c (1 - r ^ 2 / 2)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The antipodal image of a closed hemisphere is the opposite closed
hemisphere. -/
theorem finRealOrthogonalSphereMap_neg_preimage_closedHemisphere
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    (finRealOrthogonalSphereMap n
        (LinearIsometryEquiv.neg ℝ (E := FinRealEuclideanSpace n))) ⁻¹'
        finRealSphereClosedHemisphere n e =
      finRealSphereClosedHemisphere n (-e) := by
  ext x
  simp [finRealOrthogonalSphereMap, finRealSphereClosedHemisphere,
    finRealSphereClosedHalfspace, finRealSphereInnerCoordinate]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- A closed hemisphere and its opposite cover the real unit sphere. -/
theorem finRealSphereClosedHemisphere_union_opposite
    (n : ℕ) (e : FinRealEuclideanSpace n) :
    finRealSphereClosedHemisphere n e ∪
        finRealSphereClosedHemisphere n (-e) =
      Set.univ := by
  ext x
  by_cases hx : 0 ≤ finRealSphereInnerCoordinate n e x
  · simp [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace, hx]
  · have hx' : finRealSphereInnerCoordinate n e x ≤ 0 := le_of_not_ge hx
    have hop :
        0 ≤ finRealSphereInnerCoordinate n (-e) x := by
      simp [finRealSphereInnerCoordinate]
      exact hx'
    simp [finRealSphereClosedHemisphere, finRealSphereClosedHalfspace, hx, hop]

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Every closed hemisphere has surface probability at least `1/2`.

The proof uses only antipodal invariance of the normalized surface law and the
fact that a hemisphere together with its opposite covers the sphere. -/
theorem finRealSurfaceProbabilityMeasure_closedHemisphere_half
    (n : ℕ) [NeZero n] (e : FinRealEuclideanSpace n) :
    (1 / 2 : ℝ) ≤
      (finRealSurfaceProbabilityMeasure n).real
        (finRealSphereClosedHemisphere n e) := by
  let μ := finRealSurfaceProbabilityMeasure n
  let U : FinRealOrthogonalGroup n :=
    LinearIsometryEquiv.neg ℝ (E := FinRealEuclideanSpace n)
  let S : FinRealSphere n → FinRealSphere n :=
    finRealOrthogonalSphereMap n U
  have hS_meas : Measurable S := by
    dsimp [S, finRealOrthogonalSphereMap]
    exact U.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  have hH_meas :
      MeasurableSet (finRealSphereClosedHemisphere n e) :=
    measurableSet_finRealSphereClosedHemisphere n e
  have hmap :
      Measure.map S μ = μ := by
    simpa [μ, S, U] using
      finRealSurfaceProbabilityMeasure_map_orthogonal n U
  have hEqOpp :
      μ.real (finRealSphereClosedHemisphere n e) =
        μ.real (finRealSphereClosedHemisphere n (-e)) := by
    calc
      μ.real (finRealSphereClosedHemisphere n e) =
          (Measure.map S μ).real (finRealSphereClosedHemisphere n e) := by
            rw [hmap]
      _ = μ.real (S ⁻¹' finRealSphereClosedHemisphere n e) := by
            rw [map_measureReal_apply hS_meas hH_meas]
      _ = μ.real (finRealSphereClosedHemisphere n (-e)) := by
            have hpre :=
              finRealOrthogonalSphereMap_neg_preimage_closedHemisphere n e
            simpa [S, U] using congrArg (fun T => μ.real T) hpre
  have hcover :
      finRealSphereClosedHemisphere n e ∪
          finRealSphereClosedHemisphere n (-e) =
        (Set.univ : Set (FinRealSphere n)) :=
    finRealSphereClosedHemisphere_union_opposite n e
  haveI : IsProbabilityMeasure μ :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  have hunion :
      μ.real
          (finRealSphereClosedHemisphere n e ∪
            finRealSphereClosedHemisphere n (-e)) ≤
        μ.real (finRealSphereClosedHemisphere n e) +
          μ.real (finRealSphereClosedHemisphere n (-e)) :=
    measureReal_union_le _ _
  have hprob :
      μ.real
          (finRealSphereClosedHemisphere n e ∪
            finRealSphereClosedHemisphere n (-e)) = 1 := by
    rw [hcover]
    simp [μ]
  have hsum :
      (1 : ℝ) ≤ 2 * μ.real (finRealSphereClosedHemisphere n e) := by
    calc
      (1 : ℝ) =
          μ.real
            (finRealSphereClosedHemisphere n e ∪
              finRealSphereClosedHemisphere n (-e)) := hprob.symm
      _ ≤ μ.real (finRealSphereClosedHemisphere n e) +
            μ.real (finRealSphereClosedHemisphere n (-e)) := hunion
      _ = 2 * μ.real (finRealSphereClosedHemisphere n e) := by
            rw [← hEqOpp]
            ring
  nlinarith

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Geodesic half-measure enlargement bound on the concrete real sphere. -/
def FinRealSphereGeodesicIsoperimetricBound
    (n : ℕ) (μ : Measure (FinRealSphere n)) (realDim : ℝ) : Prop :=
  ∀ ⦃A : Set (FinRealSphere n)⦄, MeasurableSet A →
    (1 / 2 : ℝ) ≤ μ.real A →
    ∀ ⦃r : ℝ⦄, 0 ≤ r →
      μ.real ((finRealSphereGeodesicThickening n r A)ᶜ) ≤
        Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The single remaining deep geometric theorem: spherical caps minimize
geodesic neighbourhoods on every concrete real unit sphere.

We use only the half-measure tail consequence needed downstream: on the unit
sphere in `ℝ^n` with normalized surface probability, every measurable set of
surface mass at least `1/2` has geodesic `r`-enlargement whose complement has
mass at most
`exp (-((n - 1) r^2 / 2))`.

Everything below in this file consumes spherical isoperimetry only through
this proposition.  Proving this proposition no-input closes the real
geometric core. -/
def sphere_caps_minimize_neighborhoods : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereGeodesicIsoperimetricBound n
      (finRealSurfaceProbabilityMeasure n) (n : ℝ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Backwards-compatible name for the unique deep geometric input.

This is an abbreviation, not an additional assumption: the canonical input is
`sphere_caps_minimize_neighborhoods`. -/
abbrev FullSphericalIsoperimetry : Prop :=
  sphere_caps_minimize_neighborhoods

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Lower-camel-case compatibility name for the unique deep geometric input.

This is definitionally the same proposition as
`sphere_caps_minimize_neighborhoods`; it is not a proof of that theorem. -/
abbrev fullSphericalIsoperimetry : Prop :=
  sphere_caps_minimize_neighborhoods

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Canonical audit name for the no-input target of the real spherical
isoperimetric core.

This is definitionally the same proposition as
`sphere_caps_minimize_neighborhoods`; it is not a second geometric input. -/
abbrev finRealSphereGeodesicIsoperimetricBound_noInput : Prop :=
  sphere_caps_minimize_neighborhoods

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Half-measure cap-comparison form of spherical isoperimetry.

For every measurable set of surface mass at least `1/2`, every geodesic
radius has no larger complement than the corresponding radius-neighbourhood
of some closed hemisphere. This is the global polarization/cap-minimization
step; the separate Gaussian estimate for hemispheres is packaged below. -/
def FinRealSphereHalfMeasureHemisphereComparison
    (n : ℕ) (μ : Measure (FinRealSphere n)) : Prop :=
  ∀ ⦃A : Set (FinRealSphere n)⦄, MeasurableSet A →
    (1 / 2 : ℝ) ≤ μ.real A →
    ∀ ⦃r : ℝ⦄, 0 ≤ r →
      ∃ c : FinRealSphere n,
        μ.real ((finRealSphereGeodesicThickening n r A)ᶜ) ≤
          μ.real
            ((finRealSphereGeodesicThickening n r
              (finRealSphereClosedHemisphere n
                (c : FinRealEuclideanSpace n)))ᶜ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Dimension-at-least-two form of the half-measure cap-comparison theorem.
The degenerate real sphere `S^0` is supplied by an elementary adapter. -/
def FinRealSphereHalfMeasureHemisphereComparisonGeTwo
    (n : ℕ) (μ : Measure (FinRealSphere n)) : Prop :=
  2 ≤ n → FinRealSphereHalfMeasureHemisphereComparison n μ

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Measurable half-mass competitors for the sphere-neighbourhood variational
problem. -/
def FinRealSphereHalfMassCompetitor
    (n : ℕ) (μ : Measure (FinRealSphere n)) (A : Set (FinRealSphere n)) : Prop :=
  MeasurableSet A ∧ (1 / 2 : ℝ) ≤ μ.real A

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Complement mass of the geodesic `r`-neighbourhood of a competitor. -/
def finRealSphereNeighbourhoodComplementMass
    (n : ℕ) (μ : Measure (FinRealSphere n)) (r : ℝ)
    (A : Set (FinRealSphere n)) : ℝ :=
  μ.real ((finRealSphereGeodesicThickening n r A)ᶜ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Objective-level version of orthogonal invariance. -/
theorem finRealSphereNeighbourhoodComplementMass_orthogonal_image
    {n : ℕ} [NeZero n] (U : FinRealOrthogonalGroup n) (r : ℝ)
    (A : Set (FinRealSphere n)) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r
        (finRealOrthogonalSphereMap n U '' A) =
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A := by
  exact
    finRealSurfaceProbabilityMeasure_orthogonal_image_neighbourhoodComplement_real
      U r A

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Values of the half-mass neighbourhood-complement minimization problem. -/
def finRealSphereHalfMassComplementValues
    (n : ℕ) (μ : Measure (FinRealSphere n)) (r : ℝ) : Set ℝ :=
  {t | ∃ A : Set (FinRealSphere n),
    FinRealSphereHalfMassCompetitor n μ A ∧
      t = finRealSphereNeighbourhoodComplementMass n μ r A}

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Infimum of the half-mass neighbourhood-complement minimization problem. -/
def finRealSphereHalfMassComplementInf
    (n : ℕ) (μ : Measure (FinRealSphere n)) (r : ℝ) : ℝ :=
  sInf (finRealSphereHalfMassComplementValues n μ r)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Supremum of the half-mass neighbourhood-complement maximization problem.

This is the variational orientation used by the cap comparison theorem: caps
maximize the complement of the geodesic neighbourhood among half-mass sets. -/
def finRealSphereHalfMassComplementSup
    (n : ℕ) (μ : Measure (FinRealSphere n)) (r : ℝ) : ℝ :=
  sSup (finRealSphereHalfMassComplementValues n μ r)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Closed hemispheres are admissible half-mass competitors. -/
theorem finRealSphereHalfMassCompetitor_closedHemisphere
    (n : ℕ) [NeZero n] (e : FinRealEuclideanSpace n) :
    FinRealSphereHalfMassCompetitor n (finRealSurfaceProbabilityMeasure n)
      (finRealSphereClosedHemisphere n e) := by
  exact ⟨measurableSet_finRealSphereClosedHemisphere n e,
    finRealSurfaceProbabilityMeasure_closedHemisphere_half n e⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The half-mass minimization problem is nonempty on every concrete nonzero
real sphere. -/
theorem finRealSphereHalfMassComplementValues_nonempty_surface
    (n : ℕ) [NeZero n] (r : ℝ) :
    (finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r).Nonempty := by
  refine ⟨finRealSphereNeighbourhoodComplementMass n (finRealSurfaceProbabilityMeasure n) r
      (finRealSphereClosedHemisphere n (finRealSphereNorthPole n : FinRealEuclideanSpace n)), ?_⟩
  exact ⟨finRealSphereClosedHemisphere n (finRealSphereNorthPole n : FinRealEuclideanSpace n),
    finRealSphereHalfMassCompetitor_closedHemisphere n
      (finRealSphereNorthPole n : FinRealEuclideanSpace n), rfl⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The half-mass minimization values are bounded below by zero. -/
theorem finRealSphereHalfMassComplementValues_bddBelow
    (n : ℕ) (μ : Measure (FinRealSphere n)) (r : ℝ) :
    BddBelow (finRealSphereHalfMassComplementValues n μ r) := by
  refine ⟨0, ?_⟩
  intro t ht
  rcases ht with ⟨A, hA, rfl⟩
  exact measureReal_nonneg

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The half-mass neighbourhood-complement values for the normalized surface
law are bounded above by one. -/
theorem finRealSphereHalfMassComplementValues_bddAbove_surface
    (n : ℕ) [NeZero n] (r : ℝ) :
    BddAbove
      (finRealSphereHalfMassComplementValues n
        (finRealSurfaceProbabilityMeasure n) r) := by
  refine ⟨1, ?_⟩
  intro t ht
  rcases ht with ⟨A, _hA, rfl⟩
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasure n) :=
    finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
  exact measureReal_le_one

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Every positive tolerance admits a half-mass competitor whose neighbourhood
complement mass lies within that tolerance of the variational infimum.  This is
the minimizing-sequence form of the first isoperimetric proof step. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementInf
    (n : ℕ) [NeZero n] (r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereNeighbourhoodComplementMass n (finRealSurfaceProbabilityMeasure n) r A <
          finRealSphereHalfMassComplementInf n (finRealSurfaceProbabilityMeasure n) r + δ := by
  let values := finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r
  have hne : values.Nonempty :=
    finRealSphereHalfMassComplementValues_nonempty_surface n r
  have hlt : sInf values < sInf values + δ := by linarith
  rcases exists_lt_of_csInf_lt hne hlt with ⟨t, ht, htle⟩
  rcases ht with ⟨A, hA, rfl⟩
  exact ⟨A, hA, by simpa [finRealSphereHalfMassComplementInf, values] using htle⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The variational infimum is below the objective value of every admissible
half-mass competitor. -/
theorem finRealSphereHalfMassComplementInf_le_of_competitor
    (n : ℕ) [NeZero n] (r : ℝ)
    {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n) A) :
    finRealSphereHalfMassComplementInf n
        (finRealSurfaceProbabilityMeasure n) r ≤
      finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A := by
  let values :=
    finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r
  have hbdd : BddBelow values :=
    finRealSphereHalfMassComplementValues_bddBelow n
      (finRealSurfaceProbabilityMeasure n) r
  have hmem :
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A ∈ values := by
    exact ⟨A, hA, rfl⟩
  simpa [finRealSphereHalfMassComplementInf, values] using csInf_le hbdd hmem

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The variational supremum is above the objective value of every admissible
half-mass competitor. -/
theorem finRealSphereHalfMassComplementSup_ge_of_competitor
    (n : ℕ) [NeZero n] (r : ℝ)
    {A : Set (FinRealSphere n)}
    (hA : FinRealSphereHalfMassCompetitor n
      (finRealSurfaceProbabilityMeasure n) A) :
    finRealSphereNeighbourhoodComplementMass n
        (finRealSurfaceProbabilityMeasure n) r A ≤
      finRealSphereHalfMassComplementSup n
        (finRealSurfaceProbabilityMeasure n) r := by
  let values :=
    finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r
  have hbdd : BddAbove values :=
    finRealSphereHalfMassComplementValues_bddAbove_surface n r
  have hmem :
      finRealSphereNeighbourhoodComplementMass n
          (finRealSurfaceProbabilityMeasure n) r A ∈ values := by
    exact ⟨A, hA, rfl⟩
  simpa [finRealSphereHalfMassComplementSup, values] using le_csSup hbdd hmem

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Every positive tolerance admits a half-mass competitor whose neighbourhood
complement mass lies within that tolerance of the variational supremum.  This
is the maximizing-sequence form used by the cap-comparison proof. -/
theorem exists_finRealSphereHalfMassCompetitor_near_complementSup
    (n : ℕ) [NeZero n] (r : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Set (FinRealSphere n),
      FinRealSphereHalfMassCompetitor n (finRealSurfaceProbabilityMeasure n) A ∧
        finRealSphereHalfMassComplementSup n (finRealSurfaceProbabilityMeasure n) r - δ <
          finRealSphereNeighbourhoodComplementMass n (finRealSurfaceProbabilityMeasure n) r A := by
  let values := finRealSphereHalfMassComplementValues n (finRealSurfaceProbabilityMeasure n) r
  have hne : values.Nonempty :=
    finRealSphereHalfMassComplementValues_nonempty_surface n r
  have hlt : sSup values - δ < sSup values := by linarith
  rcases exists_lt_of_lt_csSup hne hlt with ⟨t, ht, htle⟩
  rcases ht with ⟨A, hA, rfl⟩
  exact ⟨A, hA, by simpa [finRealSphereHalfMassComplementSup, values] using htle⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- It is enough to dominate the half-mass complement supremum by one
hemisphere value at each radius. -/
theorem finRealSphereHalfMeasureHemisphereComparison_of_complementSup_le_hemisphere
    (n : ℕ) [NeZero n]
    (hSup :
      ∀ ⦃r : ℝ⦄, 0 ≤ r →
        ∃ c : FinRealSphere n,
          finRealSphereHalfMassComplementSup n
              (finRealSurfaceProbabilityMeasure n) r ≤
            finRealSphereNeighbourhoodComplementMass n
              (finRealSurfaceProbabilityMeasure n) r
              (finRealSphereClosedHemisphere n
                (c : FinRealEuclideanSpace n))) :
    FinRealSphereHalfMeasureHemisphereComparison n
      (finRealSurfaceProbabilityMeasure n) := by
  intro A hA_meas hA_half r hr
  rcases hSup hr with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hcomp :
      FinRealSphereHalfMassCompetitor n
        (finRealSurfaceProbabilityMeasure n) A :=
    ⟨hA_meas, hA_half⟩
  have hA_le_sup :=
    finRealSphereHalfMassComplementSup_ge_of_competitor n r hcomp
  exact hA_le_sup.trans hc

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Dimension-at-least-two cap comparison follows from radius-wise domination
of the complement supremum by a closed hemisphere. -/
theorem finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_hemisphere
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 ≤ r →
          ∃ c : FinRealSphere n,
            finRealSphereHalfMassComplementSup n
                (finRealSurfaceProbabilityMeasure n) r ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r
                (finRealSphereClosedHemisphere n
                  (c : FinRealEuclideanSpace n))) :
    ∀ (n : ℕ) [NeZero n],
      FinRealSphereHalfMeasureHemisphereComparisonGeTwo n
        (finRealSurfaceProbabilityMeasure n) := by
  intro n _hnNe hn2
  exact finRealSphereHalfMeasureHemisphereComparison_of_complementSup_le_hemisphere n
    (fun {r} hr => hSup (n := n) hn2 (r := r) hr)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Gaussian tail estimate for the complement of a geodesically enlarged
closed hemisphere. -/
def FinRealSphereHemisphereGaussianTail
    (n : ℕ) (μ : Measure (FinRealSphere n)) (realDim : ℝ) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, 0 ≤ r →
    μ.real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n
          (c : FinRealEuclideanSpace n)))ᶜ) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Coordinate-dominance form of the hemisphere neighbourhood complement.

For a closed hemisphere with pole `c`, the complement of its open geodesic
`r`-neighbourhood is dominated by the one-dimensional upper tail in the
opposite coordinate direction at threshold `sin r`, for positive small radii.
The endpoint `r = 0` is handled directly in the Gaussian-tail adapter below. -/
def FinRealSphereHemisphereComplementCoordinateDominance
    (n : ℕ) (μ : Measure (FinRealSphere n)) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, 0 < r → r ≤ Real.pi / 2 →
    μ.real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n
            (c : FinRealEuclideanSpace n)))ᶜ) ≤
      (finRealSphereCoordinateLaw n
        (-(c : FinRealEuclideanSpace n))).real (Set.Ici (Real.sin r))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- One-dimensional Gaussian tail form for the coordinate of a random point on
the real sphere, in the exact scale needed for the hemisphere tail. -/
def FinRealSphereCoordinateGaussianTail
    (n : ℕ) (realDim : ℝ) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, 0 ≤ r → r ≤ Real.pi / 2 →
    (finRealSphereCoordinateLaw n
      (-(c : FinRealEuclideanSpace n))).real (Set.Ici (Real.sin r)) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Interior form of the one-dimensional Gaussian tail for a spherical
coordinate.  The endpoints `r = 0` and `r = π/2` are elementary and are closed
by a separate adapter. -/
def FinRealSphereCoordinateGaussianTailInterior
    (n : ℕ) (realDim : ℝ) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, 0 < r → r < Real.pi / 2 →
    (finRealSphereCoordinateLaw n
      (-(c : FinRealEuclideanSpace n))).real (Set.Ici (Real.sin r)) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Dimension-at-least-two interior coordinate Gaussian tail.  The remaining
one-dimensional case is elementary and is supplied by an adapter in
`FinRealSphereIsoperimetryProof`. -/
def FinRealSphereCoordinateGaussianTailInteriorGeTwo
    (n : ℕ) (realDim : ℝ) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    (finRealSphereCoordinateLaw n
      (-(c : FinRealEuclideanSpace n))).real (Set.Ici (Real.sin r)) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Large-exponent interior coordinate Gaussian tail in dimensions at least
two.  The complementary exponent range is elementary: antipodal symmetry makes
each positive coordinate tail have mass at most `1/2`, and
`1/2 ≤ exp (-a)` whenever `a ≤ log 2`. -/
def FinRealSphereCoordinateGaussianTailInteriorLargeExponent
    (n : ℕ) (realDim : ℝ) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.log 2 < ((realDim - 1) * r ^ 2) / 2 →
    (finRealSphereCoordinateLaw n
      (-(c : FinRealEuclideanSpace n))).real (Set.Ici (Real.sin r)) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- North-pole form of the large-exponent coordinate tail.  Orthogonal
invariance supplies the arbitrary-pole form in `FinRealSphereIsoperimetryProof`. -/
def FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole
    (n : ℕ) [NeZero n] (realDim : ℝ) : Prop :=
  ∀ ⦃r : ℝ⦄, 2 ≤ n → 0 < r → r < Real.pi / 2 →
    Real.log 2 < ((realDim - 1) * r ^ 2) / 2 →
    (finRealSphereCoordinateLaw n
      (-(finRealSphereNorthPole n : FinRealEuclideanSpace n))).real
        (Set.Ici (Real.sin r)) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Large-radius form for the hemisphere tail.  For radii at least `π/2`, the
geodesic neighbourhood of a closed hemisphere covers the sphere up to the
boundary convention, so its complement already has the Gaussian tail. -/
def FinRealSphereHemisphereLargeRadiusTail
    (n : ℕ) (μ : Measure (FinRealSphere n)) (realDim : ℝ) : Prop :=
  ∀ (c : FinRealSphere n) ⦃r : ℝ⦄, Real.pi / 2 ≤ r →
    μ.real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n
            (c : FinRealEuclideanSpace n)))ᶜ) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Small-radius coordinate dominance, the one-dimensional coordinate tail,
and the large-radius coverage estimate imply the full hemisphere Gaussian
tail. -/
theorem finRealSphereHemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
    {n : ℕ} [NeZero n] {realDim : ℝ}
    (hDom :
      FinRealSphereHemisphereComplementCoordinateDominance n
        (finRealSurfaceProbabilityMeasure n))
    (hTail : FinRealSphereCoordinateGaussianTail n realDim)
    (hLarge :
      FinRealSphereHemisphereLargeRadiusTail n
        (finRealSurfaceProbabilityMeasure n) realDim) :
    FinRealSphereHemisphereGaussianTail n
      (finRealSurfaceProbabilityMeasure n) realDim := by
  intro c r hr
  by_cases hsmall : r ≤ Real.pi / 2
  · by_cases hr0 : r = 0
    · subst r
      haveI := finRealSurfaceProbabilityMeasure_isProbabilityMeasure n
      have hprob :
          (finRealSurfaceProbabilityMeasure n).real
              ((finRealSphereGeodesicThickening n 0
                (finRealSphereClosedHemisphere n
                  (c : FinRealEuclideanSpace n)))ᶜ) ≤ 1 :=
        measureReal_le_one
      simpa using hprob
    · have hrpos : 0 < r := lt_of_le_of_ne' hr hr0
      exact (hDom c hrpos hsmall).trans (hTail c hr hsmall)
  · exact hLarge c (le_of_lt (lt_of_not_ge hsmall))

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Cap comparison plus the explicit hemisphere tail imply the half-measure
geodesic isoperimetric bound consumed downstream. -/
theorem finRealSphereGeodesicIsoperimetricBound_of_hemisphereComparison_and_tail
    {n : ℕ} {μ : Measure (FinRealSphere n)} {realDim : ℝ}
    (hCompare : FinRealSphereHalfMeasureHemisphereComparison n μ)
    (hTail : FinRealSphereHemisphereGaussianTail n μ realDim) :
    FinRealSphereGeodesicIsoperimetricBound n μ realDim := by
  intro A hA hhalf r hr
  rcases hCompare hA hhalf hr with ⟨c, hcomp⟩
  exact hcomp.trans (hTail c hr)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the global cap-comparison step on every concrete real
sphere. -/
def sphere_halfMeasure_hemisphereComparison : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereHalfMeasureHemisphereComparison n
      (finRealSurfaceProbabilityMeasure n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the half-measure cap-comparison theorem in dimensions
at least two. -/
def sphere_halfMeasure_hemisphereComparisonGeTwo : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereHalfMeasureHemisphereComparisonGeTwo n
      (finRealSurfaceProbabilityMeasure n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input cap comparison in dimensions at least two follows from radius-wise
domination of the half-mass complement supremum by a closed hemisphere. -/
theorem sphere_halfMeasure_hemisphereComparisonGeTwo_of_complementSup_le_hemisphere
    (hSup :
      ∀ (n : ℕ) [NeZero n], 2 ≤ n →
        ∀ ⦃r : ℝ⦄, 0 ≤ r →
          ∃ c : FinRealSphere n,
            finRealSphereHalfMassComplementSup n
                (finRealSurfaceProbabilityMeasure n) r ≤
              finRealSphereNeighbourhoodComplementMass n
                (finRealSurfaceProbabilityMeasure n) r
                (finRealSphereClosedHemisphere n
                  (c : FinRealEuclideanSpace n))) :
    sphere_halfMeasure_hemisphereComparisonGeTwo :=
  finRealSphereHalfMeasureHemisphereComparisonGeTwo_of_complementSup_le_hemisphere hSup

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the Gaussian tail of geodesically enlarged
hemispheres on every concrete real sphere. -/
def sphere_hemisphereGaussianTail : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereHemisphereGaussianTail n
      (finRealSurfaceProbabilityMeasure n) (n : ℝ)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the geometric coordinate dominance of hemisphere
neighbourhood complements. -/
def sphere_hemisphereComplementCoordinateDominance : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereHemisphereComplementCoordinateDominance n
      (finRealSurfaceProbabilityMeasure n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the one-dimensional coordinate Gaussian tail on every
concrete real sphere. -/
def sphere_coordinateGaussianTail : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereCoordinateGaussianTail n (n : ℝ)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the interior one-dimensional coordinate Gaussian tail
on every concrete real sphere. -/
def sphere_coordinateGaussianTailInterior : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereCoordinateGaussianTailInterior n (n : ℝ)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the interior coordinate Gaussian tail in dimensions
at least two. -/
def sphere_coordinateGaussianTailInteriorGeTwo : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereCoordinateGaussianTailInteriorGeTwo n (n : ℝ)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the large-exponent interior coordinate Gaussian tail
in dimensions at least two. -/
def sphere_coordinateGaussianTailInteriorLargeExponent : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereCoordinateGaussianTailInteriorLargeExponent n (n : ℝ)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the north-pole large-exponent interior coordinate
Gaussian tail in dimensions at least two. -/
def sphere_coordinateGaussianTailInteriorLargeExponentNorthPole : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereCoordinateGaussianTailInteriorLargeExponentNorthPole n (n : ℝ)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- No-input package for the large-radius hemisphere neighbourhood tail. -/
def sphere_hemisphereLargeRadiusTail : Prop :=
  ∀ (n : ℕ) [NeZero n],
    FinRealSphereHemisphereLargeRadiusTail n
      (finRealSurfaceProbabilityMeasure n) (n : ℝ)

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- Small-radius coordinate dominance, the coordinate Gaussian tail, and the
large-radius hemisphere coverage estimate supply the hemisphere Gaussian tail
package. -/
theorem sphere_hemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
    (hDom : sphere_hemisphereComplementCoordinateDominance)
    (hTail : sphere_coordinateGaussianTail)
    (hLarge : sphere_hemisphereLargeRadiusTail) :
    sphere_hemisphereGaussianTail := by
  intro n hn
  exact
    finRealSphereHemisphereGaussianTail_of_coordinateDominance_and_coordinateTail
      (hDom n) (hTail n) (hLarge n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The canonical full spherical-isoperimetry input follows from the two
standard global ingredients: cap comparison and the explicit hemisphere tail. -/
theorem sphere_caps_minimize_neighborhoods_of_hemisphereComparison_and_tail
    (hCompare : sphere_halfMeasure_hemisphereComparison)
    (hTail : sphere_hemisphereGaussianTail) :
    sphere_caps_minimize_neighborhoods := by
  intro n hn
  exact
    finRealSphereGeodesicIsoperimetricBound_of_hemisphereComparison_and_tail
      (hCompare n) (hTail n)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Backwards-compatible alias of
`sphere_caps_minimize_neighborhoods_of_hemisphereComparison_and_tail` for users
working with the `FullSphericalIsoperimetry` name. -/
theorem fullSphericalIsoperimetry_of_hemisphereComparison_and_tail
    (hCompare : sphere_halfMeasure_hemisphereComparison)
    (hTail : sphere_hemisphereGaussianTail) :
    FullSphericalIsoperimetry :=
  sphere_caps_minimize_neighborhoods_of_hemisphereComparison_and_tail
    hCompare hTail

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Unpack `sphere_caps_minimize_neighborhoods` at dimension `n`. -/
theorem finRealSphereGeodesicIsoperimetricBound_of_sphere_caps_minimize_neighborhoods
    (hIso : sphere_caps_minimize_neighborhoods)
    (n : ℕ) [NeZero n] :
    FinRealSphereGeodesicIsoperimetricBound n
      (finRealSurfaceProbabilityMeasure n) (n : ℝ) :=
  hIso n

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Unpack the backwards-compatible full spherical-isoperimetry name at
dimension `n`. -/
theorem finRealSphereGeodesicIsoperimetricBound_of_fullSphericalIsoperimetry
    (hIso : FullSphericalIsoperimetry)
    (n : ℕ) [NeZero n] :
    FinRealSphereGeodesicIsoperimetricBound n
      (finRealSurfaceProbabilityMeasure n) (n : ℝ) :=
  finRealSphereGeodesicIsoperimetricBound_of_sphere_caps_minimize_neighborhoods
    hIso n

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Cap-tail estimate for a closed hemisphere under a geodesic spherical
isoperimetric bound. -/
theorem finRealSurfaceProbabilityMeasure_closedHemisphere_geodesicCapTail_le
    (n : ℕ) [NeZero n] {realDim r : ℝ}
    (e : FinRealEuclideanSpace n)
    (hIso :
      FinRealSphereGeodesicIsoperimetricBound n
        (finRealSurfaceProbabilityMeasure n) realDim)
    (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n e))ᶜ) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2)) :=
  hIso
    (measurableSet_finRealSphereClosedHemisphere n e)
    (finRealSurfaceProbabilityMeasure_closedHemisphere_half n e)
    hr

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Cap-tail estimate for a closed hemisphere from the single full spherical
isoperimetry theorem. -/
theorem finRealSurfaceProbabilityMeasure_closedHemisphere_geodesicCapTail_le_of_fullSphericalIsoperimetry
    (hIso : FullSphericalIsoperimetry)
    (n : ℕ) [NeZero n] {r : ℝ}
    (e : FinRealEuclideanSpace n)
    (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n e))ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) :=
  finRealSurfaceProbabilityMeasure_closedHemisphere_geodesicCapTail_le
    n e
    (finRealSphereGeodesicIsoperimetricBound_of_fullSphericalIsoperimetry
      hIso n)
    hr

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Named interface for the isoperimetric tail of the complement of the
geodesic `r`-neighbourhood of a closed hemisphere.  The only geometric input is
`FullSphericalIsoperimetry`. -/
theorem hemisphere_geodesic_neighborhood_complement_tail
    (hIso : FullSphericalIsoperimetry)
    (n : ℕ) [NeZero n] {r : ℝ}
    (e : FinRealEuclideanSpace n)
    (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r
          (finRealSphereClosedHemisphere n e))ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) :=
  finRealSurfaceProbabilityMeasure_closedHemisphere_geodesicCapTail_le_of_fullSphericalIsoperimetry
    hIso n e hr

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Ambient Euclidean-thickening cap-tail estimate obtained from the geodesic
cap-tail estimate and the geodesic-to-Euclidean thickening comparison. -/
theorem finRealSurfaceProbabilityMeasureAmbient_closedHemisphere_euclideanCapTail_le
    (n : ℕ) [NeZero n] {realDim r : ℝ}
    (e : FinRealEuclideanSpace n)
    (hIso :
      FinRealSphereGeodesicIsoperimetricBound n
        (finRealSurfaceProbabilityMeasure n) realDim)
    (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasureAmbient n).real
        ((Metric.thickening r
          (((↑) : FinRealSphere n → FinRealEuclideanSpace n) ''
            finRealSphereClosedHemisphere n e))ᶜ) ≤
      Real.exp (-(((realDim - 1) * r ^ 2) / 2)) :=
  (finRealSurfaceProbabilityMeasureAmbient_compl_ambientThickening_image_le_geodesic
      n r (finRealSphereClosedHemisphere n e)).trans
    (finRealSurfaceProbabilityMeasure_closedHemisphere_geodesicCapTail_le
      n e hIso hr)

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Ambient Euclidean-thickening cap-tail estimate from the single full
spherical isoperimetry theorem. -/
theorem finRealSurfaceProbabilityMeasureAmbient_closedHemisphere_euclideanCapTail_le_of_fullSphericalIsoperimetry
    (hIso : FullSphericalIsoperimetry)
    (n : ℕ) [NeZero n] {r : ℝ}
    (e : FinRealEuclideanSpace n)
    (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasureAmbient n).real
        ((Metric.thickening r
          (((↑) : FinRealSphere n → FinRealEuclideanSpace n) ''
            finRealSphereClosedHemisphere n e))ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) :=
  finRealSurfaceProbabilityMeasureAmbient_closedHemisphere_euclideanCapTail_le
    n e
    (finRealSphereGeodesicIsoperimetricBound_of_fullSphericalIsoperimetry
      hIso n)
    hr

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- Ambient Euclidean-thickening form of full spherical isoperimetry on
`ℝ^n`.

The set `A` lives in the ambient Euclidean space.  Since the ambient surface
law is supported on the unit sphere, the proof restricts `A` to the sphere,
applies the geodesic isoperimetric theorem there, and then uses the
geodesic-to-Euclidean thickening comparison. -/
theorem finRealSurfaceProbabilityMeasureAmbient_euclideanThickening_compl_le_of_fullSphericalIsoperimetry
    (hIso : FullSphericalIsoperimetry)
    (n : ℕ) [NeZero n] {A : Set (FinRealEuclideanSpace n)} {r : ℝ}
    (hA : MeasurableSet A)
    (hhalf : (1 / 2 : ℝ) ≤ (finRealSurfaceProbabilityMeasureAmbient n).real A)
    (hr : 0 ≤ r) :
    (finRealSurfaceProbabilityMeasureAmbient n).real
        ((Metric.thickening r A)ᶜ) ≤
      Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := by
  haveI : IsProbabilityMeasure (finRealSurfaceProbabilityMeasureAmbient n) :=
    finRealSurfaceProbabilityMeasureAmbient_isProbabilityMeasure n
  let B : Set (FinRealSphere n) := {x | (x : FinRealEuclideanSpace n) ∈ A}
  have hB_meas : MeasurableSet B := hA.preimage continuous_subtype_val.measurable
  have hmeasure_B :
      (finRealSurfaceProbabilityMeasure n).real B =
        (finRealSurfaceProbabilityMeasureAmbient n).real A := by
    unfold finRealSurfaceProbabilityMeasureAmbient
    rw [map_measureReal_apply continuous_subtype_val.measurable hA]
    rfl
  have hB_half :
      (1 / 2 : ℝ) ≤ (finRealSurfaceProbabilityMeasure n).real B := by
    rwa [hmeasure_B]
  have himage_subset : ((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' B ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact hu
  have hcompl_subset :
      (Metric.thickening r A)ᶜ ⊆
        (Metric.thickening r
          (((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' B))ᶜ := by
    exact Set.compl_subset_compl.mpr
      (Metric.thickening_subset_of_subset r himage_subset)
  calc
    (finRealSurfaceProbabilityMeasureAmbient n).real
        ((Metric.thickening r A)ᶜ) ≤
      (finRealSurfaceProbabilityMeasureAmbient n).real
        ((Metric.thickening r
          (((↑) : FinRealSphere n → FinRealEuclideanSpace n) '' B))ᶜ) :=
        measureReal_mono hcompl_subset
          (h₂ := (measure_lt_top (finRealSurfaceProbabilityMeasureAmbient n) _).ne)
    _ ≤ (finRealSurfaceProbabilityMeasure n).real
        ((finRealSphereGeodesicThickening n r B)ᶜ) :=
      finRealSurfaceProbabilityMeasureAmbient_compl_ambientThickening_image_le_geodesic
        n r B
    _ ≤ Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) :=
      finRealSphereGeodesicIsoperimetricBound_of_fullSphericalIsoperimetry
        hIso n hB_meas hB_half hr

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- For a singleton, geodesic thickening is the open geodesic cap. -/
theorem finRealSphereGeodesicThickening_singleton
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    finRealSphereGeodesicThickening n r ({c} : Set (FinRealSphere n)) =
      finRealSphereOpenGeodesicCap n c r := by
  ext x
  constructor
  · rintro ⟨y, hy, hdist⟩
    simpa [finRealSphereOpenGeodesicCap, Set.mem_singleton_iff.mp hy] using hdist
  · intro hx
    exact ⟨c, by simp, by simpa [finRealSphereOpenGeodesicCap] using hx⟩

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
/-- The open geodesic cap is contained in the open Euclidean/chord cap with
the same radius. -/
theorem finRealSphereOpenGeodesicCap_subset_openEuclideanCap
    (n : ℕ) (c : FinRealSphere n) (r : ℝ) :
    finRealSphereOpenGeodesicCap n c r ⊆
      finRealSphereOpenEuclideanCap n c r := by
  intro x hx
  have hgeo :
      x ∈ finRealSphereGeodesicThickening n r ({c} : Set (FinRealSphere n)) := by
    simpa [finRealSphereGeodesicThickening_singleton n c r] using hx
  have hmetric := finRealSphereGeodesicThickening_subset_metricThickening
    n r ({c} : Set (FinRealSphere n)) hgeo
  rcases Metric.mem_thickening_iff.mp hmetric with ⟨y, hy, hdist⟩
  have hyc : y = c := Set.mem_singleton_iff.mp hy
  simpa [finRealSphereOpenEuclideanCap, hyc] using hdist

/-! ## Real-sphere surface law API

The names above are sample-matrix names.  The geometric core of Appendix B is
really the real Hilbert--Schmidt sphere of the underlying finite-dimensional
real normed space.  The following aliases expose that real-sphere layer
explicitly, without changing the underlying objects or normalizations.
-/

omit [DecidableEq p] [DecidableEq q] in
/-- The unnormalised real surface measure on the Frobenius unit sphere of the
sample-matrix space.  This is exactly Mathlib's `toSphere` measure for the
ambient additive Haar measure, only with a geometry-facing name. -/
abbrev realSurfaceMeasure :
    Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
  sampleSurfaceMeasure (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The normalized real surface probability measure on the Frobenius unit
sphere. -/
abbrev realSurfaceProbabilityMeasure :
    Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
  sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The normalized real surface probability measure transported to the
ambient sample-matrix space by the sphere inclusion. -/
abbrev realSurfaceProbabilityMeasureAmbient :
    Measure (SampleMatrix p q σ) :=
  sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The real surface probability measure is a probability measure. -/
theorem realSurfaceProbabilityMeasure_isProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    IsProbabilityMeasure
      (realSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) :=
  sampleSurfaceProbabilityMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient real surface law is a probability measure. -/
theorem realSurfaceProbabilityMeasureAmbient_isProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    IsProbabilityMeasure
      (realSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) :=
  sampleSurfaceProbabilityMeasureAmbient_isProbabilityMeasure (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- Transport from the subtype sphere to the ambient real Hilbert--Schmidt
space.  This is the exact bridge used whenever the project switches between
observables on the sphere subtype and observables on the ambient matrix space. -/
theorem realSurfaceProbabilityMeasure_transport_to_ambient :
    Measure.map
        ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
        (realSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
      realSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ) := by
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient real surface law is supported on the real Frobenius unit
sphere. -/
theorem realSurfaceProbabilityMeasureAmbient_sphere
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    realSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)
        (Metric.sphere (0 : SampleMatrix p q σ) 1) = 1 :=
  sampleSurfaceProbabilityMeasureAmbient_sphere (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The real surface law is invariant under every real linear isometry of the
ambient Hilbert--Schmidt space. -/
theorem realSurfaceProbabilityMeasure_map_linearIsometryEquiv
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ) :
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        (realSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
      realSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ) :=
  sampleSurfaceProbabilityMeasure_map_linearIsometryEquiv (p := p) (q := q) (σ := σ) U

omit [DecidableEq p] [DecidableEq q] in
/-- The ambient real surface law is invariant under every real linear
isometry of the Hilbert--Schmidt space. -/
theorem realSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (U : SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ) :
    Measure.map U
        (realSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) =
      realSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ) :=
  sampleSurfaceProbabilityMeasureAmbient_map_linearIsometryEquiv
    (p := p) (q := q) (σ := σ) U

omit [DecidableEq p] [DecidableEq q] in
/-- The flattened complex-coordinate isometry, viewed as a real linear
isometry. -/
def sampleMatrixComplexLinearIsometryEquivRestrictScalarsReal :
    SampleMatrix p q σ ≃ₗᵢ[ℝ] EuclideanSpace ℂ (SampleCoord p q σ) := by
  let U := sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)
  refine LinearIsometryEquiv.mk ?e ?norm
  · refine
      { toFun := U
        invFun := U.symm
        left_inv := U.left_inv
        right_inv := U.right_inv
        map_add' := ?_
        map_smul' := ?_ }
    · intro x y
      exact U.map_add x y
    · intro a x
      change U (((a : ℂ) • x)) = ((a : ℂ) • U x)
      exact U.map_smul (a : ℂ) x
  · intro x
    exact U.norm_map x

omit [DecidableEq p] [DecidableEq q] in
/-- The standard real-coordinate isometry from the Hilbert--Schmidt sample
matrix space to the concrete real Euclidean space with the same finrank. -/
noncomputable def sampleMatrixRealStdRepr :
    SampleMatrix p q σ ≃ₗᵢ[ℝ]
      FinRealEuclideanSpace (Module.finrank ℝ (SampleMatrix p q σ)) := by
  classical
  have hcard :
      Fintype.card (SampleCoord p q σ × Fin 2) =
        Module.finrank ℝ (SampleMatrix p q σ) := by
    unfold SampleCoord SampleMatrix BipIndex
    simp only [Module.finrank_matrix, Complex.finrank_real_complex,
      Fintype.card_prod, Fintype.card_fin]
  exact
    (sampleMatrixComplexLinearIsometryEquivRestrictScalarsReal
        (p := p) (q := q) (σ := σ)).trans
      ((complexRealCoordLinearIsometryEquiv (SampleCoord p q σ)).symm.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          ((Fintype.equivFin (SampleCoord p q σ × Fin 2)).trans
            (finCongr hcard))))

omit [DecidableEq p] [DecidableEq q] in
/-- The normalized Frobenius-sphere surface law transports under the standard
real-coordinate isometry to the canonical real-sphere surface law. -/
theorem sampleSurfaceProbabilityMeasure_map_sampleMatrixRealStdRepr
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    Measure.map
        (Subtype.map
          (sampleMatrixRealStdRepr (p := p) (q := q) (σ := σ))
          (fun _ hx => by simpa using hx))
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
      finRealSurfaceProbabilityMeasure
        (Module.finrank ℝ (SampleMatrix p q σ)) := by
  classical
  let E := SampleMatrix p q σ
  let n := Module.finrank ℝ E
  let U : E ≃ₗᵢ[ℝ] FinRealEuclideanSpace n :=
    sampleMatrixRealStdRepr (p := p) (q := q) (σ := σ)
  let μ : Measure E := sampleHaarMeasure (p := p) (q := q) (σ := σ)
  let ν : Measure (FinRealEuclideanSpace n) := finRealHaarMeasure n
  haveI : μ.IsAddHaarMeasure := by
    unfold μ sampleHaarMeasure
    infer_instance
  haveI : ν.IsAddHaarMeasure := by
    unfold ν finRealHaarMeasure
    infer_instance
  have hsurj : Function.Surjective U.toLinearEquiv.toLinearMap :=
    U.toLinearEquiv.surjective
  obtain ⟨c, hcpos, hmap⟩ :=
    U.toLinearEquiv.toLinearMap.exists_map_addHaar_eq_smul_addHaar
      (μ := μ) (ν := ν) hsurj
  have hmapU : Measure.map U μ = c • ν := by
    simpa using hmap
  have hc0 : c ≠ 0 := ne_of_gt hcpos
  have hball_nonempty : (Metric.ball (0 : FinRealEuclideanSpace n) 1).Nonempty :=
    ⟨0, by simp⟩
  have hνball_ne_zero : ν (Metric.ball (0 : FinRealEuclideanSpace n) 1) ≠ 0 := by
    exact Metric.isOpen_ball.measure_ne_zero ν hball_nonempty
  have hμball_lt_top : μ (Metric.ball (0 : E) 1) < ∞ := by
    exact lt_of_le_of_lt
      (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall (0 : E) 1).measure_lt_top)
  have hpre_ball :
      U ⁻¹' Metric.ball (0 : FinRealEuclideanSpace n) 1 =
        Metric.ball (0 : E) 1 := by
    ext x
    simp [Metric.mem_ball, dist_eq_norm, U]
  have hball_eq :
      μ (Metric.ball (0 : E) 1) =
        c * ν (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
    calc
      μ (Metric.ball (0 : E) 1) =
          Measure.map U μ (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
        rw [Measure.map_apply U.continuous.measurable Metric.isOpen_ball.measurableSet]
        rw [hpre_ball]
      _ = (c • ν) (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
        rw [hmapU]
      _ = c * ν (Metric.ball (0 : FinRealEuclideanSpace n) 1) := by
        simp [smul_eq_mul]
  have hctop : c ≠ ∞ := by
    intro hc
    have hright :
        c * ν (Metric.ball (0 : FinRealEuclideanSpace n) 1) = ∞ := by
      rw [hc]
      simp [hνball_ne_zero]
    have hμtop : μ (Metric.ball (0 : E) 1) = ∞ := by
      rw [hball_eq, hright]
    exact hμball_lt_top.ne hμtop
  have hE_nontrivial : Nontrivial E := by infer_instance
  have hn_pos : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  change
    Measure.map
        (Subtype.map U (fun _ hx => by simpa using hx))
        μ.toSphere.toFinite =
      ν.toSphere.toFinite
  exact
    map_toFinite_toSphere_linearIsometryEquiv_of_map_eq_smul
      (μ := μ) (ν := ν) U hc0 hctop hmapU

omit [DecidableEq p] [DecidableEq q] in
/-- Ambient version of
`sampleSurfaceProbabilityMeasure_map_sampleMatrixRealStdRepr`. -/
theorem sampleSurfaceProbabilityMeasureAmbient_map_sampleMatrixRealStdRepr
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    Measure.map
        (sampleMatrixRealStdRepr (p := p) (q := q) (σ := σ))
        (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) =
      finRealSurfaceProbabilityMeasureAmbient
        (Module.finrank ℝ (SampleMatrix p q σ)) := by
  classical
  let U := sampleMatrixRealStdRepr (p := p) (q := q) (σ := σ)
  have hsub :=
    sampleSurfaceProbabilityMeasure_map_sampleMatrixRealStdRepr
      (p := p) (q := q) (σ := σ)
  unfold sampleSurfaceProbabilityMeasureAmbient finRealSurfaceProbabilityMeasureAmbient
  rw [← hsub]
  rw [Measure.map_map U.continuous.measurable continuous_subtype_val.measurable]
  rw [Measure.map_map
    continuous_subtype_val.measurable
    ((U.continuous.subtype_map (fun _ hx => by simpa using hx)).measurable)]
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Direct SampleMatrix transport of full real-sphere isoperimetry.

This is the reusable matrix-space form: any measurable set of the ambient
Hilbert--Schmidt sphere law with mass at least `1/2` has Euclidean/Frobenius
`r`-neighbourhood complement bounded by the sharp real-sphere Gaussian tail.
The proof is just the exact measure transport by `sampleMatrixRealStdRepr`. -/
theorem sampleSurfaceProbabilityMeasureAmbient_euclideanThickening_compl_le_of_fullSphericalIsoperimetry
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hIso : FullSphericalIsoperimetry)
    {A : Set (SampleMatrix p q σ)} {r : ℝ}
    (hA : MeasurableSet A)
    (hhalf :
      (1 / 2 : ℝ) ≤
        (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real A)
    (hr : 0 ≤ r) :
    (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real
        ((Metric.thickening r A)ᶜ) ≤
      Real.exp
        (-((((Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1) * r ^ 2) / 2)) := by
  classical
  let E := SampleMatrix p q σ
  let n := Module.finrank ℝ E
  let U : E ≃ₗᵢ[ℝ] FinRealEuclideanSpace n :=
    sampleMatrixRealStdRepr (p := p) (q := q) (σ := σ)
  have hn_pos : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  haveI : IsProbabilityMeasure
      (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) :=
    sampleSurfaceProbabilityMeasureAmbient_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  have hmap :
      Measure.map U
          (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) =
        finRealSurfaceProbabilityMeasureAmbient n := by
    exact sampleSurfaceProbabilityMeasureAmbient_map_sampleMatrixRealStdRepr
      (p := p) (q := q) (σ := σ)
  let B : Set (FinRealEuclideanSpace n) := {Y | U.symm Y ∈ A}
  have hB_meas : MeasurableSet B := hA.preimage U.symm.continuous.measurable
  have hB_half :
      (1 / 2 : ℝ) ≤ (finRealSurfaceProbabilityMeasureAmbient n).real B := by
    have hreal :
        (finRealSurfaceProbabilityMeasureAmbient n).real B =
          (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real A := by
      rw [← hmap]
      rw [map_measureReal_apply U.continuous.measurable hB_meas]
      congr 1
      ext X
      simp [B, U]
    rwa [hreal]
  have hfinTail :
      (finRealSurfaceProbabilityMeasureAmbient n).real
          ((Metric.thickening r B)ᶜ) ≤
        Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) :=
    finRealSurfaceProbabilityMeasureAmbient_euclideanThickening_compl_le_of_fullSphericalIsoperimetry
      hIso n hB_meas hB_half hr
  have hthick_meas : MeasurableSet ((Metric.thickening r B)ᶜ) :=
    Metric.isOpen_thickening.measurableSet.compl
  have hpre_eq :
      (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real
          (U ⁻¹' ((Metric.thickening r B)ᶜ)) =
        (finRealSurfaceProbabilityMeasureAmbient n).real
          ((Metric.thickening r B)ᶜ) := by
    rw [← hmap]
    rw [map_measureReal_apply U.continuous.measurable hthick_meas]
  have hsubset :
      ((Metric.thickening r A)ᶜ) ⊆ U ⁻¹' ((Metric.thickening r B)ᶜ) := by
    intro X hX
    rw [Set.mem_preimage, Set.mem_compl_iff]
    intro hthick
    rw [Metric.mem_thickening_iff] at hthick
    rcases hthick with ⟨Y, hYB, hdist⟩
    have hYA : U.symm Y ∈ A := by
      simpa [B] using hYB
    have hdist_eq : dist (U X) Y = dist X (U.symm Y) := by
      simpa only [U.apply_symm_apply] using
        (U.isometry.dist_eq X (U.symm Y))
    have hdist' : dist X (U.symm Y) < r := by
      simpa [hdist_eq] using hdist
    exact hX (by
      rw [Metric.mem_thickening_iff]
      exact ⟨U.symm Y, hYA, hdist'⟩)
  calc
    (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real
        ((Metric.thickening r A)ᶜ) ≤
      (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)).real
        (U ⁻¹' ((Metric.thickening r B)ᶜ)) :=
        measureReal_mono hsubset
          (h₂ := (measure_lt_top
            (sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)) _).ne)
    _ = (finRealSurfaceProbabilityMeasureAmbient n).real
          ((Metric.thickening r B)ᶜ) := hpre_eq
    _ ≤ Real.exp (-((((n : ℝ) - 1) * r ^ 2) / 2)) := hfinTail

/-! ## True polar-coordinate theorem for the sample-matrix space -/

omit [DecidableEq p] [DecidableEq q] in
/-- Genuine polar-coordinate theorem for the finite-dimensional sample-matrix
space.  Under the homeomorphism
`x ↦ (x / ‖x‖, ‖x‖)` from the punctured space to
`S × (0,∞)`, additive Haar measure becomes surface measure times the radial
measure with density `r^(N-1)`.

This is the geometric disintegration theorem supplied by Mathlib; it is
no-input and foundation-clean. -/
theorem sample_polar_coordinates_measurePreserving
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    MeasurePreserving (homeomorphUnitSphereProd (SampleMatrix p q σ))
      ((sampleHaarMeasure (p := p) (q := q) (σ := σ)).comap Subtype.val)
      ((sampleSurfaceMeasure (p := p) (q := q) (σ := σ)).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (SampleMatrix p q σ) - 1))) := by
  unfold sampleSurfaceMeasure sampleHaarMeasure
  exact Measure.measurePreserving_homeomorphUnitSphereProd
    ((Module.finBasis ℝ (SampleMatrix p q σ)).addHaar)

omit [DecidableEq p] [DecidableEq q] in
/-- Total mass of the unnormalized surface measure, in Mathlib's canonical
normalization. -/
theorem sampleSurfaceMeasure_apply_univ
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    sampleSurfaceMeasure (p := p) (q := q) (σ := σ) Set.univ =
      Module.finrank ℝ (SampleMatrix p q σ) *
        sampleHaarMeasure (p := p) (q := q) (σ := σ)
          (Metric.ball (0 : SampleMatrix p q σ) 1) := by
  unfold sampleSurfaceMeasure sampleHaarMeasure
  exact Measure.toSphere_apply_univ
    ((Module.finBasis ℝ (SampleMatrix p q σ)).addHaar :
      Measure (SampleMatrix p q σ))

end AppendixB
end PptFactorization
