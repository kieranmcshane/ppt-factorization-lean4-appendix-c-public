import PptFactorization.AppendixBSurfaceMeasure
import PptFactorization.AppendixBSphericalLevy
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Appendix B: polar and global-Levy bridge

This file is deliberately small and canonical.  It does not assert spherical
isoperimetry.  Instead, it proves the exact transport lemmas that connect:

* the canonical surface probability measure on the Hilbert--Schmidt sphere;
* the concrete Gaussian-direction spherical law used elsewhere in the repo;
* the global median-centered Levy theorem consumed by the localized Levy
  reduction.

Thus the remaining analytic input is the expected one: the global Levy theorem
for the canonical sphere.  The Gaussian polar law is proved below from unitary
invariance and uniqueness of invariant probability measure on the sphere.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace AppendixB

open RandomMatrixModel GaussianModel HighProbabilityBounds

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## Global Levy predicates -/

omit [DecidableEq p] [DecidableEq q] in
/-- Identify the Frobenius unit sphere of sample matrices with the unit sphere
of the flattened complex Euclidean coordinate space. -/
def sampleMatrixSphereEquiv :
    Metric.sphere (0 : SampleMatrix p q σ) 1 ≃
      Metric.sphere (0 : EuclideanSpace ℂ (SampleCoord p q σ)) 1 where
  toFun x :=
    ⟨sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ) x, by
      have hx : ‖(x : SampleMatrix p q σ)‖ = 1 := by
        rw [← dist_zero_right (a := (x : SampleMatrix p q σ))]
        change (x : SampleMatrix p q σ) ∈ Metric.sphere (0 : SampleMatrix p q σ) 1
        exact x.property
      rw [Metric.mem_sphere, dist_eq_norm]
      simp only [sub_zero]
      calc
        ‖sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)
            (x : SampleMatrix p q σ)‖ = ‖(x : SampleMatrix p q σ)‖ :=
          (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).norm_map
            (x : SampleMatrix p q σ)
        _ = 1 := hx⟩
  invFun y :=
    ⟨(sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm y, by
      have hy : ‖(y : EuclideanSpace ℂ (SampleCoord p q σ))‖ = 1 := by
        rw [← dist_zero_right (a := (y : EuclideanSpace ℂ (SampleCoord p q σ)))]
        change (y : EuclideanSpace ℂ (SampleCoord p q σ)) ∈
          Metric.sphere (0 : EuclideanSpace ℂ (SampleCoord p q σ)) 1
        exact y.property
      rw [Metric.mem_sphere, dist_eq_norm]
      simp only [sub_zero]
      calc
        ‖(sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm
            (y : EuclideanSpace ℂ (SampleCoord p q σ))‖ =
          ‖(y : EuclideanSpace ℂ (SampleCoord p q σ))‖ :=
          (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm.norm_map
            (y : EuclideanSpace ℂ (SampleCoord p q σ))
        _ = 1 := hy⟩
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro y
    ext
    simp

omit [DecidableEq p] [DecidableEq q] in
/-- Transport a unitary on flattened Gaussian coordinates to a complex linear
isometry of the sample-matrix Hilbert space. -/
def sampleCoordUnitaryLinearIsometryEquiv
    [DecidableEq (SampleCoord p q σ)]
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ :=
  ((sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).trans
    (matrixUnitaryLinearIsometryEquiv U)).trans
      (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm

omit [DecidableEq p] [DecidableEq q] in
/-- The same transported unitary, viewed as a real linear isometry of the
underlying Frobenius normed real vector space. -/
def sampleCoordUnitaryRealLinearIsometryEquiv
    [DecidableEq (SampleCoord p q σ)]
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    SampleMatrix p q σ ≃ₗᵢ[ℝ] SampleMatrix p q σ :=
  IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    ((sampleCoordUnitaryLinearIsometryEquiv (p := p) (q := q) (σ := σ) U).toIsometryEquiv)
    (by simp)

omit [DecidableEq p] [DecidableEq q] in
/-- The Frobenius unit sphere of sample matrices is homeomorphic to the unit
sphere of the flattened complex coordinate space. -/
def sampleMatrixSphereHomeomorph :
    Metric.sphere (0 : SampleMatrix p q σ) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℂ (SampleCoord p q σ)) 1 where
  toEquiv := sampleMatrixSphereEquiv (p := p) (q := q) (σ := σ)
  continuous_toFun := by
    simpa using
      ((sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).continuous.subtype_map
        (fun _ hx => by simpa using hx))
  continuous_invFun := by
    have hcont :
        Continuous
          ((sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm) :=
      (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm.continuous
    simpa using hcont.subtype_map (fun _ hy => by simpa using hy)

instance instSampleCoordUnitaryGroupSampleSphereSMul
    [DecidableEq (SampleCoord p q σ)] :
    SMul (Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
      (Metric.sphere (0 : SampleMatrix p q σ) 1) where
  smul U x :=
    (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ)).symm
      (U • (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x))

instance instSampleCoordUnitaryGroupSampleSphereMulAction
    [DecidableEq (SampleCoord p q σ)] :
    MulAction (Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
      (Metric.sphere (0 : SampleMatrix p q σ) 1) where
  one_smul := by
    intro x
    change
      (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ)).symm
          ((1 : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) •
            (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x)) = x
    simp
  mul_smul := by
    intro U V x
    apply (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ)).injective
    change
      ((U * V : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) •
        (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x)) =
      U • (V • (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x))
    simpa using (smul_smul U V
      (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x)).symm

instance instSampleCoordUnitaryGroupSampleSphereContinuousSMul
    [DecidableEq (SampleCoord p q σ)] :
    ContinuousSMul (Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
      (Metric.sphere (0 : SampleMatrix p q σ) 1) where
  continuous_smul := by
    let e := sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ)
    change Continuous (fun z :
        Matrix.unitaryGroup (SampleCoord p q σ) ℂ ×
          Metric.sphere (0 : SampleMatrix p q σ) 1 =>
        e.symm (z.1 • e z.2))
    exact e.continuous_invFun.comp (continuous_fst.smul (e.continuous_toFun.comp continuous_snd))

instance instSampleCoordUnitaryGroupSampleSphereMeasurableConstSMul
    [DecidableEq (SampleCoord p q σ)] :
    MeasurableConstSMul (Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
      (Metric.sphere (0 : SampleMatrix p q σ) 1) where
  measurable_const_smul g := (continuous_const_smul g).measurable

instance instSampleCoordUnitaryGroupSampleSpherePretransitive
    [DecidableEq (SampleCoord p q σ)] [Nonempty p] [Nonempty q] [Nonempty σ] :
    MulAction.IsPretransitive (Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
      (Metric.sphere (0 : SampleMatrix p q σ) 1) := by
  let e := sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ)
  refine ⟨?_⟩
  intro x y
  rcases MulAction.exists_smul_eq
      (Matrix.unitaryGroup (SampleCoord p q σ) ℂ) (e x) (e y) with ⟨U, hU⟩
  refine ⟨U, ?_⟩
  apply e.injective
  change U • e x = e y
  simpa using hU

omit [DecidableEq p] [DecidableEq q] in
/-- The transported unitary action on the sample-matrix sphere agrees, after
forgetting the subtype, with the ambient real linear isometry coming from the
same unitary on flattened coordinates. -/
theorem sampleSphere_val_smul
    [DecidableEq (SampleCoord p q σ)]
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 =>
      ((U • x : Metric.sphere (0 : SampleMatrix p q σ) 1) : SampleMatrix p q σ)) =
      fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 =>
        sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
          (x : SampleMatrix p q σ) := by
  funext x
  change
    (((sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ)).symm
        (U • (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x))) :
          SampleMatrix p q σ) =
      sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
        (x : SampleMatrix p q σ)
  change
    (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm
        (((U • (sampleMatrixSphereHomeomorph (p := p) (q := q) (σ := σ) x) :
            Metric.sphere (0 : EuclideanSpace ℂ (SampleCoord p q σ)) 1) :
              EuclideanSpace ℂ (SampleCoord p q σ))) =
      sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
        (x : SampleMatrix p q σ)
  change
    (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)).symm
        (matrixUnitaryLinearIsometryEquiv U
          (sampleMatrixComplexLinearIsometryEquiv (p := p) (q := q) (σ := σ)
            (x : SampleMatrix p q σ))) =
      sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
        (x : SampleMatrix p q σ)
  simp [sampleCoordUnitaryRealLinearIsometryEquiv, sampleCoordUnitaryLinearIsometryEquiv,
    matrixUnitaryLinearIsometryEquiv_apply,
    IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero]

omit [DecidableEq p] [DecidableEq q] in
/-- The transported unitary action on the sample-matrix sphere is the subtype
map induced by the corresponding ambient real linear isometry. -/
theorem sampleSphere_smul_eq_subtypeMap
    [DecidableEq (SampleCoord p q σ)]
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x) =
      Subtype.map
        (sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U)
        (fun x hx => by
          have hx' : ‖x‖ = 1 := by
            rw [← dist_zero_right (a := x)]
            change x ∈ Metric.sphere (0 : SampleMatrix p q σ) 1
            exact hx
          rw [Metric.mem_sphere, dist_eq_norm]
          simp only [sub_zero]
          calc
            ‖sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U x‖ =
                ‖x‖ :=
              (sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U).norm_map x
            _ = 1 := hx') := by
  funext x
  apply Subtype.ext
  exact congrFun (sampleSphere_val_smul (p := p) (q := q) (σ := σ) U) x

/-- The ambient version of the canonical uniform surface law. -/
abbrev surfaceModelMeasure : Measure (SampleMatrix p q σ) :=
  sampleSurfaceProbabilityMeasureAmbient (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The canonical ambient surface law is a probability measure in the
nondegenerate case. -/
theorem surfaceModelMeasure_isProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    IsProbabilityMeasure
      (surfaceModelMeasure (p := p) (q := q) (σ := σ)) :=
  sampleSurfaceProbabilityMeasureAmbient_isProbabilityMeasure
    (p := p) (q := q) (σ := σ)

omit [DecidableEq p] [DecidableEq q] in
/-- The canonical surface probability measure on the sample-matrix sphere is
invariant under the transported unitary action. -/
theorem sampleSurfaceProbabilityMeasure_map_sampleCoordUnitary
    [Nonempty p] [Nonempty q] [Nonempty σ]
    [DecidableEq (SampleCoord p q σ)]
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    Measure.map
        (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) =
      sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ) := by
  rw [sampleSphere_smul_eq_subtypeMap (p := p) (q := q) (σ := σ) U]
  simpa using
    sampleSurfaceProbabilityMeasure_map_linearIsometryEquiv
      (p := p) (q := q) (σ := σ)
      (sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U)

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian direction law on the sample-matrix sphere is invariant under
the same transported unitary action. -/
theorem gaussianSphericalSubtypeMeasure_map_sampleCoordUnitary
    [Nonempty p] [Nonempty q] [Nonempty σ]
    [DecidableEq (SampleCoord p q σ)]
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    Measure.map
        (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
        (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) =
      gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) := by
  let S : Metric.sphere (0 : SampleMatrix p q σ) 1 →
      Metric.sphere (0 : SampleMatrix p q σ) 1 := fun x => U • x
  let Uℂ :=
    sampleCoordUnitaryLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
  let Uℝ :=
    sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
  have hsphere :
      MeasurableSet (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
    Metric.isClosed_sphere.measurableSet
  have hval :
      ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) ∘ S =
        Uℝ ∘ ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) := by
    funext x
    exact congrFun (sampleSphere_val_smul (p := p) (q := q) (σ := σ) U) x
  have hpush :
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map S (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))) =
        Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
    calc
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map S (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))) =
        Measure.map
          (((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) ∘ S)
          (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
          simpa [Function.comp, S] using
            (Measure.map_map
              (μ := gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))
              (f := S)
              (g := ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
              continuous_subtype_val.measurable
              (continuous_const_smul U).measurable)
      _ =
        Measure.map
          (Uℝ ∘ ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
          (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
          rw [hval]
      _ =
        Measure.map Uℝ
          (Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
            (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))
              (f := ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
              (g := Uℝ)
              Uℝ.continuous.measurable
              continuous_subtype_val.measurable)
      _ =
        Measure.map Uℝ
          ((gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)).restrict
            (Metric.sphere (0 : SampleMatrix p q σ) 1)) := by
          unfold gaussianSphericalSubtypeMeasure
          rw [map_comap_subtype_coe hsphere]
      _ =
        Measure.map Uℝ
          (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
          haveI :
              IsProbabilityMeasure
                (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) :=
            gaussianDirection_law_isProbabilityMeasure (p := p) (q := q) (σ := σ)
          have hmem :
              Metric.sphere (0 : SampleMatrix p q σ) 1 ∈
                ae (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
            exact
              (mem_ae_iff_prob_eq_one hsphere).2
                (gaussianDirection_law_sphere (p := p) (q := q) (σ := σ))
          exact congrArg (Measure.map Uℝ) (Measure.restrict_eq_self_of_ae_mem hmem)
      _ = gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ) := by
          simpa [Uℂ, Uℝ, sampleCoordUnitaryRealLinearIsometryEquiv] using
            (gaussianDirection_law_map_complexLinearIsometryEquiv
              (p := p) (q := q) (σ := σ) Uℂ)
      _ =
        Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
          unfold gaussianSphericalSubtypeMeasure
          rw [map_comap_subtype_coe hsphere]
          haveI :
              IsProbabilityMeasure
                (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) :=
            gaussianDirection_law_isProbabilityMeasure (p := p) (q := q) (σ := σ)
          have hmem :
              Metric.sphere (0 : SampleMatrix p q σ) 1 ∈
                ae (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
            exact
              (mem_ae_iff_prob_eq_one hsphere).2
                (gaussianDirection_law_sphere (p := p) (q := q) (σ := σ))
          exact (Measure.restrict_eq_self_of_ae_mem hmem).symm
  have hcomap := congrArg
    (Measure.comap ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
    hpush
  have hleft :
      Measure.comap ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
            (Measure.map S (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)))) =
        Measure.map S (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
    simpa [hsphere] using
      (MeasurableEmbedding.subtype_coe hsphere).comap_map
        (Measure.map S (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)))
  have hright :
      Measure.comap ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
            (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))) =
        gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) := by
    simpa [hsphere] using
      (MeasurableEmbedding.subtype_coe hsphere).comap_map
        (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))
  exact hleft.symm.trans (hcomap.trans hright)

omit [DecidableEq p] [DecidableEq q] in
/-- The Gaussian spherical subtype law and the canonical surface probability
measure coincide by uniqueness of invariant probability measures on the compact
homogeneous sphere. -/
theorem gaussianSphericalSubtypeMeasure_eq_sampleSurfaceProbabilityMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) =
      sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ) := by
  classical
  letI : DecidableEq (SampleCoord p q σ) := Classical.decEq _
  haveI :
      IsProbabilityMeasure
        (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) :=
    gaussianSphericalSubtypeMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  haveI :
      IsProbabilityMeasure
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) :=
    sampleSurfaceProbabilityMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
  exact invariant_probabilityMeasure_eq_of_compact_pretransitive
    (G := Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
    (X := Metric.sphere (0 : SampleMatrix p q σ) 1)
    (μ := gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))
    (σ := sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ))
    (fun U => ⟨(continuous_const_smul U).measurable,
      gaussianSphericalSubtypeMeasure_map_sampleCoordUnitary
        (p := p) (q := q) (σ := σ) U⟩)
    (fun U => ⟨(continuous_const_smul U).measurable,
      sampleSurfaceProbabilityMeasure_map_sampleCoordUnitary
        (p := p) (q := q) (σ := σ) U⟩)

omit [DecidableEq p] [DecidableEq q] in
/-- Gaussian polar law: the ambient Gaussian direction measure agrees with the
canonical ambient surface probability measure. -/
theorem polarLaw
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    sphericalModelMeasure (p := p) (q := q) (σ := σ) =
      surfaceModelMeasure (p := p) (q := q) (σ := σ) := by
  let hsphere :
      MeasurableSet (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
    Metric.isClosed_sphere.measurableSet
  calc
    sphericalModelMeasure (p := p) (q := q) (σ := σ) =
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
        (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
        unfold sphericalModelMeasure gaussianSphericalSubtypeMeasure
        rw [map_comap_subtype_coe hsphere]
        haveI :
            IsProbabilityMeasure
              (sphericalModelMeasure (p := p) (q := q) (σ := σ)) :=
          sphericalModelMeasure_isProbabilityMeasure (p := p) (q := q) (σ := σ)
        have hmem :
            Metric.sphere (0 : SampleMatrix p q σ) 1 ∈
              ae (sphericalModelMeasure (p := p) (q := q) (σ := σ)) := by
          exact
            (mem_ae_iff_prob_eq_one hsphere).2
              (gaussianDirection_law_sphere (p := p) (q := q) (σ := σ))
        exact (Measure.restrict_eq_self_of_ae_mem hmem).symm
    _ =
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) := by
        rw [gaussianSphericalSubtypeMeasure_eq_sampleSurfaceProbabilityMeasure
          (p := p) (q := q) (σ := σ)]
    _ = surfaceModelMeasure (p := p) (q := q) (σ := σ) := by
        rfl

/-! ## Radial slices and Gaussian radius-direction independence -/

omit [DecidableEq p] [DecidableEq q] in
/-- The radial slice `{G : ‖G‖₂ ∈ s}` in the sample-matrix space. -/
def sampleMatrixRadialSet (s : Set ℝ) : Set (SampleMatrix p q σ) :=
  {G | frobeniusNorm G ∈ s}

omit [DecidableEq p] [DecidableEq q] in
theorem measurableSet_sampleMatrixRadialSet {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet (sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s) := by
  have hmeas : Measurable (fun G : SampleMatrix p q σ => frobeniusNorm G) := by
    unfold frobeniusNorm
    fun_prop
  exact hmeas hs

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianMatrix_preimage_sampleMatrixRadialSet (s : Set ℝ) :
    gaussianMatrix p q σ ⁻¹'
        sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s =
      gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s := by
  ext ω
  rfl

omit [DecidableEq p] [DecidableEq q] in
theorem sampleMatrixRadialSet_preimage_complexLinearIsometryEquiv
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ)
    (s : Set ℝ) :
    U ⁻¹' sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s =
      sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s := by
  ext G
  simp [sampleMatrixRadialSet, frobeniusNorm]

omit [DecidableEq p] [DecidableEq q] in
/-- The concrete Gaussian matrix law, viewed on the ambient sample-matrix
space. -/
def gaussianMatrixLaw : Measure (SampleMatrix p q σ) :=
  (gaussianMeasure p q σ).map (gaussianMatrix p q σ)

omit [DecidableEq p] [DecidableEq q] in
/-- Restriction of the Gaussian matrix law to a radial event. -/
def gaussianMatrixRadialSliceMeasure (s : Set ℝ) : Measure (SampleMatrix p q σ) :=
  (gaussianMatrixLaw (p := p) (q := q) (σ := σ)).restrict
    (sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s)

omit [DecidableEq p] [DecidableEq q] in
/-- The direction law obtained from the Gaussian matrix after restricting to a
radial event. -/
def gaussianSphericalSliceMeasure (s : Set ℝ) : Measure (SampleMatrix p q σ) :=
  (gaussianMatrixRadialSliceMeasure (p := p) (q := q) (σ := σ) s).map
    (normalizedSample (p := p) (q := q) (σ := σ))

omit [DecidableEq p] [DecidableEq q] in
/-- The same radial-slice direction law, now living directly on the unit-sphere
subtype. -/
def gaussianSphericalSubtypeSliceMeasure (s : Set ℝ) :
    Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
  (gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s).comap Subtype.val

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSliceMeasure_apply
    {s : Set ℝ} (hs : MeasurableSet s) {t : Set (SampleMatrix p q σ)}
    (ht : MeasurableSet t) :
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s t =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s ∩
          gaussianDirection (p := p) (q := q) (σ := σ) ⁻¹' t) := by
  let μG : Measure (SampleMatrix p q σ) := gaussianMatrixLaw (p := p) (q := q) (σ := σ)
  unfold gaussianSphericalSliceMeasure gaussianMatrixRadialSliceMeasure gaussianMatrixLaw
  rw [Measure.map_apply
    (measurable_normalizedSample (p := p) (q := q) (σ := σ)) ht]
  rw [Measure.restrict_apply
    ((measurable_normalizedSample (p := p) (q := q) (σ := σ)) ht)]
  rw [Measure.map_apply (measurable_gaussianMatrix (p := p) (q := q) (σ := σ))]
  · congr 1
    ext ω
    simp [gaussianRadius, gaussianDirection, sampleMatrixRadialSet, and_comm]
  · exact
      ((measurable_normalizedSample (p := p) (q := q) (σ := σ)) ht).inter
        (measurableSet_sampleMatrixRadialSet (p := p) (q := q) (σ := σ) hs)

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSliceMeasure_apply_univ
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s Set.univ =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
  rw [gaussianSphericalSliceMeasure_apply (p := p) (q := q) (σ := σ) hs
    MeasurableSet.univ]
  simp

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianMatrixLaw_zero
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    gaussianMatrixLaw (p := p) (q := q) (σ := σ)
        ({0} : Set (SampleMatrix p q σ)) = 0 := by
  have hzeroMatrix :
      sampleMatrixOfRealCoordinates (p := p) (q := q) (σ := σ) 0 = 0 := by
    ext i α
    simp [GaussianModel.sampleMatrixOfRealCoordinates, GaussianModel.complexGaussianScale]
  have hsingleton :
      gaussianMatrix p q σ ⁻¹' ({0} : Set (SampleMatrix p q σ)) = ({0} : Set (Ω p q σ)) := by
    ext ω
    constructor
    · intro hω
      have h0 : gaussianMatrix p q σ 0 = 0 := by
        simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix] using hzeroMatrix
      exact gaussianMatrix_injective (p := p) (q := q) (σ := σ) (hω.trans h0.symm)
    · intro hω
      rcases Set.mem_singleton_iff.mp hω with rfl
      simpa [gaussianMatrix, GaussianModel.gaussianSampleMatrix] using hzeroMatrix
  unfold gaussianMatrixLaw
  rw [Measure.map_apply
    (measurable_gaussianMatrix (p := p) (q := q) (σ := σ))
    (measurableSet_singleton 0)]
  haveI : MeasureTheory.NoAtoms (gaussianMeasure p q σ) :=
    gaussianMeasure_noAtoms (p := p) (q := q) (σ := σ)
  simpa [hsingleton] using
    (MeasureTheory.measure_singleton (μ := gaussianMeasure p q σ) (0 : Ω p q σ))

omit [DecidableEq p] [DecidableEq q] in
theorem normalizedSample_preimage_sphere_compl_subset :
    (normalizedSample (p := p) (q := q) (σ := σ)) ⁻¹'
        (Metric.sphere (0 : SampleMatrix p q σ) 1)ᶜ ⊆
      ({0} : Set (SampleMatrix p q σ)) := by
  intro G hG
  by_contra hG0
  exact hG (normalizedSample_mem_sphere_of_ne_zero
    (p := p) (q := q) (σ := σ) hG0)

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSliceMeasure_sphere
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s
        (Metric.sphere (0 : SampleMatrix p q σ) 1) = 
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
  have hcomp :
      gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s
          (Metric.sphere (0 : SampleMatrix p q σ) 1)ᶜ = 0 := by
    unfold gaussianSphericalSliceMeasure gaussianMatrixRadialSliceMeasure gaussianMatrixLaw
    rw [Measure.map_apply
      (measurable_normalizedSample (p := p) (q := q) (σ := σ))
      (Metric.isClosed_sphere.measurableSet.compl)]
    rw [Measure.restrict_apply
      ((measurable_normalizedSample (p := p) (q := q) (σ := σ))
        (Metric.isClosed_sphere.measurableSet.compl))]
    refine measure_mono_null
      (t := ({0} : Set (SampleMatrix p q σ)) ∩
        sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s) ?_ ?_
    · intro G hG
      exact ⟨normalizedSample_preimage_sphere_compl_subset
        (p := p) (q := q) (σ := σ) hG.1, hG.2⟩
    · have hzero :
          gaussianMatrixLaw (p := p) (q := q) (σ := σ)
              (({0} : Set (SampleMatrix p q σ)) ∩
                sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s) = 0 := by
        exact measure_mono_null Set.inter_subset_left
          (gaussianMatrixLaw_zero (p := p) (q := q) (σ := σ))
      exact hzero
  haveI :
      IsFiniteMeasure
        (gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s) := by
    refine ⟨?_⟩
    haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
      rw [gaussianMeasure_eq]
      infer_instance
    rw [gaussianSphericalSliceMeasure_apply_univ (p := p) (q := q) (σ := σ) hs]
    exact measure_lt_top _ _
  calc
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s
        (Metric.sphere (0 : SampleMatrix p q σ) 1) =
      gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s Set.univ := by
        simpa using measure_of_measure_compl_eq_zero hcomp
    _ =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
        exact gaussianSphericalSliceMeasure_apply_univ (p := p) (q := q) (σ := σ) hs

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSubtypeSliceMeasure_apply_univ
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s Set.univ =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
  unfold gaussianSphericalSubtypeSliceMeasure
  rw [Measure.comap_apply Subtype.val Subtype.val_injective]
  · simpa [Metric.sphere] using
      gaussianSphericalSliceMeasure_sphere (p := p) (q := q) (σ := σ) hs
  · intro u hu
    exact
      (MeasurableEmbedding.subtype_coe
        (Metric.isClosed_sphere.measurableSet :
          MeasurableSet (Metric.sphere (0 : SampleMatrix p q σ) 1))).measurableSet_image' hu
  · simp

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSubtypeSliceMeasure_isFiniteMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    IsFiniteMeasure
      (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
  refine ⟨?_⟩
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  rw [gaussianSphericalSubtypeSliceMeasure_apply_univ (p := p) (q := q) (σ := σ) hs]
  exact measure_lt_top _ _

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianMatrixRadialSliceMeasure_map_complexLinearIsometryEquiv
    {s : Set ℝ} (hs : MeasurableSet s)
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ) :
    Measure.map U
        (gaussianMatrixRadialSliceMeasure (p := p) (q := q) (σ := σ) s) =
      gaussianMatrixRadialSliceMeasure (p := p) (q := q) (σ := σ) s := by
  ext t ht
  unfold gaussianMatrixRadialSliceMeasure
  rw [Measure.map_apply U.continuous.measurable ht]
  rw [Measure.restrict_apply (U.continuous.measurable ht), Measure.restrict_apply ht]
  have hmap :=
    congrArg
      (fun ν : Measure (SampleMatrix p q σ) =>
        ν (t ∩ sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s))
      (gaussianMatrixLaw_map_complexLinearIsometryEquiv
        (p := p) (q := q) (σ := σ) U)
  have hmap' :
      gaussianMatrixLaw (p := p) (q := q) (σ := σ)
          (U ⁻¹' (t ∩ sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s)) =
        gaussianMatrixLaw (p := p) (q := q) (σ := σ)
          (t ∩ sampleMatrixRadialSet (p := p) (q := q) (σ := σ) s) := by
    simpa [Measure.map_apply U.continuous.measurable
      (ht.inter (measurableSet_sampleMatrixRadialSet (p := p) (q := q) (σ := σ) hs))] using hmap
  simpa [Set.preimage_inter,
    sampleMatrixRadialSet_preimage_complexLinearIsometryEquiv
      (p := p) (q := q) (σ := σ) U s] using hmap'

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSliceMeasure_map_complexLinearIsometryEquiv
    {s : Set ℝ} (hs : MeasurableSet s)
    (U : SampleMatrix p q σ ≃ₗᵢ[ℂ] SampleMatrix p q σ) :
    Measure.map U
        (gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s) =
      gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s := by
  exact
    normalizedSample_pushforward_map_complexLinearIsometryEquiv_of_map_eq
      (p := p) (q := q) (σ := σ)
      (μ := gaussianMatrixRadialSliceMeasure (p := p) (q := q) (σ := σ) s)
      U
      (gaussianMatrixRadialSliceMeasure_map_complexLinearIsometryEquiv
        (p := p) (q := q) (σ := σ) hs U)

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSliceMeasure_ae_mem_sphere
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    Metric.sphere (0 : SampleMatrix p q σ) 1 ∈
      ae (gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s) := by
  haveI :
      IsFiniteMeasure
        (gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s) := by
    refine ⟨?_⟩
    haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
      rw [gaussianMeasure_eq]
      infer_instance
    rw [gaussianSphericalSliceMeasure_apply_univ (p := p) (q := q) (σ := σ) hs]
    exact measure_lt_top _ _
  rw [mem_ae_iff]
  calc
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s
        (Metric.sphere (0 : SampleMatrix p q σ) 1)ᶜ =
      gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s Set.univ -
        gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s
          (Metric.sphere (0 : SampleMatrix p q σ) 1) := by
        simpa using
          (measure_compl
            (μ := gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s)
            Metric.isClosed_sphere.measurableSet
            (measure_lt_top _ _).ne)
    _ =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) -
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
        rw [gaussianSphericalSliceMeasure_apply_univ (p := p) (q := q) (σ := σ) hs,
          gaussianSphericalSliceMeasure_sphere (p := p) (q := q) (σ := σ) hs]
    _ = 0 := by simp

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSubtypeSliceMeasure_map_sampleCoordUnitary
    [Nonempty p] [Nonempty q] [Nonempty σ]
    [DecidableEq (SampleCoord p q σ)]
    {s : Set ℝ} (hs : MeasurableSet s)
    (U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ) :
    Measure.map
        (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
        (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) =
      gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s := by
  let S : Metric.sphere (0 : SampleMatrix p q σ) 1 →
      Metric.sphere (0 : SampleMatrix p q σ) 1 := fun x => U • x
  let Uℂ :=
    sampleCoordUnitaryLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
  let Uℝ :=
    sampleCoordUnitaryRealLinearIsometryEquiv (p := p) (q := q) (σ := σ) U
  have hsphere :
      MeasurableSet (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
    Metric.isClosed_sphere.measurableSet
  have hval :
      ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) ∘ S =
        Uℝ ∘ ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) := by
    funext x
    exact congrFun (sampleSphere_val_smul (p := p) (q := q) (σ := σ) U) x
  have hpush :
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map S
            (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)) =
        Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
    calc
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map S
            (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)) =
        Measure.map
          (((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ) ∘ S)
          (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
          simpa [Function.comp, S] using
            (Measure.map_map
              (μ := gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)
              (f := S)
              (g := ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
              continuous_subtype_val.measurable
              (continuous_const_smul U).measurable)
      _ =
        Measure.map
          (Uℝ ∘ ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
          (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
          rw [hval]
      _ =
        Measure.map Uℝ
          (Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
            (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)) := by
          symm
          simpa [Function.comp] using
            (Measure.map_map
              (μ := gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)
              (f := ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
              (g := Uℝ)
              Uℝ.continuous.measurable
              continuous_subtype_val.measurable)
      _ =
        Measure.map Uℝ
          ((gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s).restrict
            (Metric.sphere (0 : SampleMatrix p q σ) 1)) := by
          unfold gaussianSphericalSubtypeSliceMeasure
          rw [map_comap_subtype_coe hsphere]
      _ =
        Measure.map Uℝ
          (gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s) := by
          exact congrArg (Measure.map Uℝ)
            (Measure.restrict_eq_self_of_ae_mem
              (gaussianSphericalSliceMeasure_ae_mem_sphere
                (p := p) (q := q) (σ := σ) hs))
      _ = gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s := by
          simpa [Uℂ, Uℝ, sampleCoordUnitaryRealLinearIsometryEquiv] using
            (gaussianSphericalSliceMeasure_map_complexLinearIsometryEquiv
              (p := p) (q := q) (σ := σ) hs Uℂ)
      _ =
        Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
          unfold gaussianSphericalSubtypeSliceMeasure
          rw [map_comap_subtype_coe hsphere]
          exact (Measure.restrict_eq_self_of_ae_mem
            (gaussianSphericalSliceMeasure_ae_mem_sphere
              (p := p) (q := q) (σ := σ) hs)).symm
  have hcomap := congrArg
    (Measure.comap ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ))
    hpush
  have hleft :
      Measure.comap ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
            (Measure.map S
              (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s))) =
        Measure.map S
          (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
    simpa [hsphere] using
      (MeasurableEmbedding.subtype_coe hsphere).comap_map
        (Measure.map S
          (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s))
  have hright :
      Measure.comap ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
            (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)) =
        gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s := by
    simpa [hsphere] using
      (MeasurableEmbedding.subtype_coe hsphere).comap_map
        (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s)
  exact hleft.symm.trans (hcomap.trans hright)

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSubtypeSliceMeasure_eq_smul_gaussianSphericalSubtypeMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
        gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) := by
  classical
  by_cases hzero :
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) = 0
  · ext t ht
    have hleft_le :
        gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s t ≤
          gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s Set.univ :=
      measure_mono (Set.subset_univ t)
    rw [gaussianSphericalSubtypeSliceMeasure_apply_univ
      (p := p) (q := q) (σ := σ) hs, hzero] at hleft_le
    have hleft :
        gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s t = 0 :=
      le_antisymm hleft_le bot_le
    rw [Measure.smul_apply, smul_eq_mul, hleft, hzero]
    simp
  · letI : DecidableEq (SampleCoord p q σ) := Classical.decEq _
    letI : Nontrivial (SampleMatrix p q σ) := by infer_instance
    letI : Nonempty (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
      by
        simpa using
          (NormedSpace.sphere_nonempty_rclike
            (𝕜 := ℂ) (E := SampleMatrix p q σ) (r := (1 : ℝ)) (by norm_num))
    let μs : MeasureTheory.FiniteMeasure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
      ⟨gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s,
        gaussianSphericalSubtypeSliceMeasure_isFiniteMeasure
          (p := p) (q := q) (σ := σ) hs⟩
    let μP : MeasureTheory.ProbabilityMeasure (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
      μs.normalize
    let μPmeas : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1) := (μP : Measure _)
    have hmass :
        (μs.mass : ℝ≥0∞) =
          gaussianMeasure p q σ
            (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
      calc
        (μs.mass : ℝ≥0∞) = (μs : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1)) Set.univ := by
          exact MeasureTheory.FiniteMeasure.ennreal_mass (μ := μs)
        _ =
          gaussianMeasure p q σ
            (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) := by
            exact gaussianSphericalSubtypeSliceMeasure_apply_univ
              (p := p) (q := q) (σ := σ) hs
    have hμs_ne : μs ≠ 0 := by
      intro hz
      have hmass0 : μs.mass = 0 := by
        rw [hz]
        simp
      have hmass0' : (μs.mass : ℝ≥0∞) = 0 := by
        exact_mod_cast hmass0
      rw [hmass] at hmass0'
      exact hzero hmass0'
    have hμP_inv :
        ∀ U : Matrix.unitaryGroup (SampleCoord p q σ) ℂ,
          MeasurePreserving
            (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
            μPmeas μPmeas := by
      intro U
      refine ⟨(continuous_const_smul U).measurable, ?_⟩
      have hnorm0 :
          μPmeas =
            μs.mass⁻¹ •
              (μs : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1)) := by
        change
          (((μs.normalize :
            MeasureTheory.ProbabilityMeasure
              (Metric.sphere (0 : SampleMatrix p q σ) 1)) :
            Measure (Metric.sphere (0 : SampleMatrix p q σ) 1))) =
            μs.mass⁻¹ •
              (μs : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1))
        exact μs.toMeasure_normalize_eq_of_nonzero hμs_ne
      have hnorm :
          μPmeas =
            μs.mass⁻¹ •
              gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s := by
        simpa [μs] using hnorm0
      calc
        Measure.map (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
            μPmeas =
          Measure.map (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
            (μs.mass⁻¹ •
              gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
              rw [hnorm]
        _ =
          μs.mass⁻¹ •
            Measure.map (fun x : Metric.sphere (0 : SampleMatrix p q σ) 1 => U • x)
              (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
              rw [Measure.map_smul]
        _ =
          μs.mass⁻¹ •
            gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s := by
              rw [gaussianSphericalSubtypeSliceMeasure_map_sampleCoordUnitary
                (p := p) (q := q) (σ := σ) hs U]
        _ =
          μPmeas := by
              rw [hnorm]
    have hEq :
        μPmeas =
          gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) := by
      haveI :
          IsProbabilityMeasure
            (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) :=
        gaussianSphericalSubtypeMeasure_isProbabilityMeasure
          (p := p) (q := q) (σ := σ)
      exact invariant_probabilityMeasure_eq_of_compact_pretransitive
        (G := Matrix.unitaryGroup (SampleCoord p q σ) ℂ)
        (X := Metric.sphere (0 : SampleMatrix p q σ) 1)
        (μ := μPmeas)
        (σ := gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ))
        hμP_inv
        (fun U => ⟨(continuous_const_smul U).measurable,
          gaussianSphericalSubtypeMeasure_map_sampleCoordUnitary
            (p := p) (q := q) (σ := σ) U⟩)
    have hslice :
        gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s =
          μs.mass • μPmeas := by
      have h0 :=
        congrArg
          (fun ν : MeasureTheory.FiniteMeasure (Metric.sphere (0 : SampleMatrix p q σ) 1) =>
            (ν : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1)))
          (μs.self_eq_mass_smul_normalize)
      have h :
          (μs : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1)) =
            μs.mass • μPmeas := by
        change
          (μs : Measure (Metric.sphere (0 : SampleMatrix p q σ) 1)) =
            μs.mass •
              (((μs.normalize :
                MeasureTheory.ProbabilityMeasure
                  (Metric.sphere (0 : SampleMatrix p q σ) 1)) :
                Measure (Metric.sphere (0 : SampleMatrix p q σ) 1)))
        exact h0
      simpa [μs] using h
    calc
      gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s =
        μs.mass • μPmeas :=
        hslice
      _ =
        μs.mass • gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) := by
          rw [hEq]
      _ =
        gaussianMeasure p q σ
          (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
          gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) := by
          change
            (μs.mass : ℝ≥0∞) •
                gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ) =
              gaussianMeasure p q σ
                (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
                gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)
          rw [hmass]

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianSphericalSliceMeasure_eq_smul_sphericalModelMeasure
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
        sphericalModelMeasure (p := p) (q := q) (σ := σ) := by
  have hsphere :
      MeasurableSet (Metric.sphere (0 : SampleMatrix p q σ) 1) :=
    Metric.isClosed_sphere.measurableSet
  have hmapSubtype :
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) =
        sphericalModelMeasure (p := p) (q := q) (σ := σ) := by
    unfold sphericalModelMeasure gaussianSphericalSubtypeMeasure
    rw [map_comap_subtype_coe hsphere]
    haveI :
        IsProbabilityMeasure
          (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) :=
      gaussianDirection_law_isProbabilityMeasure (p := p) (q := q) (σ := σ)
    have hmem :
        Metric.sphere (0 : SampleMatrix p q σ) 1 ∈
          ae (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
      exact
        (mem_ae_iff_prob_eq_one hsphere).2
          (gaussianDirection_law_sphere (p := p) (q := q) (σ := σ))
    exact Measure.restrict_eq_self_of_ae_mem hmem
  calc
    gaussianSphericalSliceMeasure (p := p) (q := q) (σ := σ) s =
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
        (gaussianSphericalSubtypeSliceMeasure (p := p) (q := q) (σ := σ) s) := by
        unfold gaussianSphericalSubtypeSliceMeasure
        rw [map_comap_subtype_coe hsphere]
        exact (Measure.restrict_eq_self_of_ae_mem
          (gaussianSphericalSliceMeasure_ae_mem_sphere
            (p := p) (q := q) (σ := σ) hs)).symm
    _ =
      Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
        (gaussianMeasure p q σ
          (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
          gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
          rw [gaussianSphericalSubtypeSliceMeasure_eq_smul_gaussianSphericalSubtypeMeasure
            (p := p) (q := q) (σ := σ) hs]
    _ =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
        Measure.map ((↑) : Metric.sphere (0 : SampleMatrix p q σ) 1 → SampleMatrix p q σ)
          (gaussianSphericalSubtypeMeasure (p := p) (q := q) (σ := σ)) := by
          rw [Measure.map_smul]
    _ =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) •
        sphericalModelMeasure (p := p) (q := q) (σ := σ) := by
          rw [hmapSubtype]

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianRadius_direction_measure_inter_preimage_eq_mul
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {s : Set ℝ} {t : Set (SampleMatrix p q σ)}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    gaussianMeasure p q σ
      (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s ∩
        gaussianDirection (p := p) (q := q) (σ := σ) ⁻¹' t) =
      gaussianMeasure p q σ
        (gaussianRadius (p := p) (q := q) (σ := σ) ⁻¹' s) *
      gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ) t := by
  rw [← gaussianSphericalSliceMeasure_apply
    (p := p) (q := q) (σ := σ) hs ht]
  rw [gaussianSphericalSliceMeasure_eq_smul_sphericalModelMeasure
    (p := p) (q := q) (σ := σ) hs]
  simp [sphericalModelMeasure, smul_eq_mul]

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianRadius_indep_gaussianDirection
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
      gaussianDirection (p := p) (q := q) (σ := σ) := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have h :=
    gaussianRadius_direction_measure_inter_preimage_eq_mul
    (p := p) (q := q) (σ := σ) hs ht
  rw [gaussianSphericalSampleMeasure, Measure.map_apply
    (measurable_gaussianDirection (p := p) (q := q) (σ := σ)) ht] at h
  exact h

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianRadius_direction_map_prod_eq_prod_map_map
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    (gaussianMeasure p q σ).map
        (fun ω => (gaussianRadius (p := p) (q := q) (σ := σ) ω,
          gaussianDirection (p := p) (q := q) (σ := σ) ω)) =
      ((gaussianMeasure p q σ).map (gaussianRadius (p := p) (q := q) (σ := σ))).prod
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
  haveI : IsFiniteMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  exact
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_gaussianRadius (p := p) (q := q) (σ := σ)).aemeasurable
      (measurable_gaussianDirection (p := p) (q := q) (σ := σ)).aemeasurable).mp
      (gaussianRadius_indep_gaussianDirection (p := p) (q := q) (σ := σ))

omit [DecidableEq p] [DecidableEq q] in
theorem gaussianRadiusSq_indep_gaussianDirection
    [Nonempty p] [Nonempty q] [Nonempty σ] :
    gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
      gaussianDirection (p := p) (q := q) (σ := σ) := by
  exact gaussianRadiusSq_indep_gaussianDirection_of_gaussianRadius_indep
    (p := p) (q := q) (σ := σ)
    (gaussianRadius_indep_gaussianDirection (p := p) (q := q) (σ := σ))

omit [DecidableEq p] [DecidableEq q] in
/-- Powers of the Gaussian mass are independent of the Gaussian direction.

This is the no-hypothesis polar independence input needed for the
Gaussian-to-spherical radial normalization of homogeneous PT moments. -/
theorem gaussianMass_pow_indep_gaussianDirection
    [Nonempty p] [Nonempty q] [Nonempty σ] (k : ℕ) :
    (fun ω : Ω p q σ => gaussianMass p q σ ω ^ k) ⟂ᵢ[gaussianMeasure p q σ]
      gaussianDirection (p := p) (q := q) (σ := σ) := by
  have h :=
    (gaussianRadiusSq_indep_gaussianDirection (p := p) (q := q) (σ := σ)).comp
      ((measurable_id : Measurable (fun r : ℝ => r)).pow_const k)
      measurable_id
  simpa [gaussianRadiusSq_eq_gaussianMass, Function.comp_def] using h

omit [DecidableEq p] [DecidableEq q] in
/-- Exact no-hypothesis factorization for homogeneous radial powers:
`E[T^k F(G/‖G‖)] = E[T^k] E[F(X)]`, where
`T = ‖G‖₂²` and `X = G/‖G‖₂`.

The theorem is stated for the concrete Gaussian direction law used by the
project; `sphericalModelMeasure` is definitionally this law. -/
theorem gaussianMass_pow_radial_spherical_factorization
    [Nonempty p] [Nonempty q] [Nonempty σ] (k : ℕ)
    {F : SampleMatrix p q σ → ℝ}
    (hF :
      AEStronglyMeasurable F
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ))) :
    ∫ ω : Ω p q σ,
        gaussianMass p q σ ω ^ k *
          F (gaussianDirection (p := p) (q := q) (σ := σ) ω)
        ∂gaussianMeasure p q σ =
      (∫ ω : Ω p q σ, gaussianMass p q σ ω ^ k ∂gaussianMeasure p q σ) *
        (∫ X : SampleMatrix p q σ,
          F X ∂gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ)) := by
  have hR :
      AEMeasurable (fun ω : Ω p q σ => gaussianMass p q σ ω ^ k)
        (gaussianMeasure p q σ) := by
    have h :
        Measurable
          (fun ω : Ω p q σ =>
            gaussianRadiusSq (p := p) (q := q) (σ := σ) ω ^ k) :=
      measurable_gaussianRadiusSq.pow_const k
    simpa [gaussianRadiusSq_eq_gaussianMass] using h.aemeasurable
  exact radial_spherical_integral_factorization_of_indep
    (μ := gaussianMeasure p q σ)
    (R := fun ω : Ω p q σ => gaussianMass p q σ ω ^ k)
    (X := gaussianDirection (p := p) (q := q) (σ := σ))
    (F := F)
    (gaussianMass_pow_indep_gaussianDirection (p := p) (q := q) (σ := σ) k)
    hR
    measurable_gaussianDirection.aemeasurable
    hF

/-- Global median-centered Levy concentration for real-valued Lipschitz
observables on an ambient probability measure.  This is the exact shape needed
by `AppendixBSphericalLevy`. -/
def GlobalSphericalLevy
    (μ : Measure (SampleMatrix p q σ)) (n : ℝ) : Prop :=
  ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
    LipschitzWith K g →
      ∀ {u : ℝ}, 0 < u →
        ∃ Mg,
          _root_.AppendixB.IsMedian μ g Mg ∧
            μ.real {X | u ≤ |g X - Mg|} ≤
              2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))

/-- Strong global median-centered Levy concentration for ambient observables.

The median is chosen once for a Lipschitz observable and then works
simultaneously for every tail radius.  This is the paper-shaped form of the
global Levy input; `GlobalSphericalLevy` is the weaker theorem-level API used
by the existing localized reduction. -/
def StrongGlobalSphericalLevy
    (μ : Measure (SampleMatrix p q σ)) (n : ℝ) : Prop :=
  ∀ {g : SampleMatrix p q σ → ℝ} {K : ℝ≥0},
    LipschitzWith K g →
      ∃ Mg,
        _root_.AppendixB.IsMedian μ g Mg ∧
          ∀ {u : ℝ}, 0 < u →
            μ.real {X | u ≤ |g X - Mg|} ≤
              2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))

omit [DecidableEq p] [DecidableEq q] in
/-- The strong global Levy input immediately gives the weaker existing API. -/
theorem StrongGlobalSphericalLevy.toGlobalSphericalLevy
    {μ : Measure (SampleMatrix p q σ)} {n : ℝ}
    (h : StrongGlobalSphericalLevy (p := p) (q := q) (σ := σ) μ n) :
    GlobalSphericalLevy (p := p) (q := q) (σ := σ) μ n := by
  intro g K hg u hu
  rcases h hg with ⟨Mg, hMg, hTail⟩
  exact ⟨Mg, hMg, hTail hu⟩

omit [DecidableEq p] [DecidableEq q] in
/-- Effective real sphere dimension for the canonical surface Levy theorem.

The surface lives on the unit sphere inside the real Hilbert space underlying
`SampleMatrix p q σ`, so the geometric sphere dimension is the ambient real
dimension minus one.  We keep this as a named API constant so later comparison
lemmas can weaken it to the pipeline exponent using
`GlobalSurfaceSubtypeLevy.mono`. -/
noncomputable def surfaceLevyDimension : ℝ :=
  (Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1

omit [Fintype p] [Fintype q] [Fintype σ] [DecidableEq p] [DecidableEq q] in
@[simp] theorem surfaceLevyDimension_eq :
    surfaceLevyDimension (p := p) (q := q) (σ := σ) =
      (Module.finrank ℝ (SampleMatrix p q σ) : ℝ) - 1 :=
  rfl

omit [DecidableEq p] [DecidableEq q] in
@[simp] theorem surfaceLevyDimension_eq_two_mul_bipartiteDimension_mul_sampleDimension_sub_one :
    surfaceLevyDimension (p := p) (q := q) (σ := σ) =
      2 * bipartiteDimension p q * sampleDimension σ - 1 := by
  unfold surfaceLevyDimension HighProbabilityBounds.bipartiteDimension
    HighProbabilityBounds.sampleDimension
  simp only [RandomMatrixModel.SampleMatrix, Module.finrank_matrix,
    Complex.finrank_real_complex, Nat.cast_mul, Nat.cast_ofNat]
  ring

omit [DecidableEq p] [DecidableEq q] in
/-- A sufficient condition comparing the paper's pipeline exponent
`cDim * d^4` to the geometric sphere dimension.  The final pipeline assumptions
do not imply this on their own; one needs an additional sample-size lower bound
of order `cDim * d^2`. -/
theorem pipelineLevyDimension_le_surfaceLevyDimension_of_sampleDimension
    {cDim d : ℝ}
    (hDim : bipartiteDimension p q = d ^ 2)
    (hSample : cDim * d ^ 2 ≤ 2 * sampleDimension σ - 1)
    (hOne : 1 ≤ d ^ 2) :
    cDim * d ^ 4 ≤ surfaceLevyDimension (p := p) (q := q) (σ := σ) := by
  rw [surfaceLevyDimension_eq_two_mul_bipartiteDimension_mul_sampleDimension_sub_one, hDim]
  have hmul :
      cDim * d ^ 4 ≤ (2 * sampleDimension σ - 1) * d ^ 2 := by
    have hnonneg : 0 ≤ d ^ 2 := by positivity
    calc
      cDim * d ^ 4 = (cDim * d ^ 2) * d ^ 2 := by ring
      _ ≤ (2 * sampleDimension σ - 1) * d ^ 2 :=
        mul_le_mul_of_nonneg_right hSample hnonneg
  calc
    cDim * d ^ 4 ≤ (2 * sampleDimension σ - 1) * d ^ 2 := hmul
    _ = 2 * sampleDimension σ * d ^ 2 - d ^ 2 := by ring
    _ ≤ 2 * sampleDimension σ * d ^ 2 - 1 := by linarith
    _ = 2 * d ^ 2 * sampleDimension σ - 1 := by ring

/-- Global median-centered Levy concentration directly on the unit-sphere
subtype carrying the canonical surface probability measure. -/
def GlobalSurfaceSubtypeLevy
    (n : ℝ) : Prop :=
  ∀ {g : Metric.sphere (0 : SampleMatrix p q σ) 1 → ℝ} {K : ℝ≥0},
    LipschitzWith K g →
      ∀ {u : ℝ}, 0 < u →
        ∃ Mg,
          _root_.AppendixB.IsMedian
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
                {X | u ≤ |g X - Mg|} ≤
              2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))

omit [DecidableEq p] [DecidableEq q] in
/-- Monotonicity of the surface Levy API in the dimension/exponent parameter.

A Levy theorem with a larger exponent parameter implies the same theorem with
any smaller parameter, since the right-hand exponential tail bound only gets
weaker. -/
theorem GlobalSurfaceSubtypeLevy.mono
    {n m : ℝ}
    (hnm : n ≤ m)
    (h : GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) m) :
    GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n := by
  intro g K hg u hu
  rcases h hg hu with ⟨Mg, hMg, hTail⟩
  refine ⟨Mg, hMg, hTail.trans ?_⟩
  let c : ℝ := u ^ 2 / (4 * (K : ℝ) ^ 2)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hmul : n * c ≤ m * c :=
    mul_le_mul_of_nonneg_right hnm hc_nonneg
  have hExp :
      Real.exp (-(m * c)) ≤ Real.exp (-(n * c)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm :
      m * u ^ 2 / (4 * (K : ℝ) ^ 2) = m * c := by
    dsimp [c]
    ring
  have hn :
      n * u ^ 2 / (4 * (K : ℝ) ^ 2) = n * c := by
    dsimp [c]
    ring
  calc
    2 * Real.exp (-(m * u ^ 2 / (4 * (K : ℝ) ^ 2)))
        = 2 * Real.exp (-(m * c)) := by rw [hm]
    _ ≤ 2 * Real.exp (-(n * c)) :=
        mul_le_mul_of_nonneg_left hExp (by norm_num)
    _ = 2 * Real.exp (-(n * u ^ 2 / (4 * (K : ℝ) ^ 2))) := by rw [hn]

/-- Strong global median-centered Levy concentration on the canonical surface
sphere.

This is the mathematically natural fixed-median surface theorem: for every
Lipschitz observable on the sphere there is a median whose Levy tail bound
holds for all positive radii at once.  It is an abbreviation, so the
paper-facing theorem below can package an independently proved spherical
isoperimetric statement without adding another definitional layer. -/
abbrev StrongGlobalSurfaceSubtypeLevy
    (n : ℝ) : Prop :=
  ∀ {g : Metric.sphere (0 : SampleMatrix p q σ) 1 → ℝ} {K : ℝ≥0},
    LipschitzWith K g →
      ∃ Mg,
        _root_.AppendixB.IsMedian
          (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
          ∀ {u : ℝ}, 0 < u →
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
                {X | u ≤ |g X - Mg|} ≤
              2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))

omit [DecidableEq p] [DecidableEq q] in
/-- Package a fixed-median spherical Levy theorem as the strong surface API.

This is the intended theorem-level entry point for the geometric input: once
the spherical isoperimetric/concentration theorem has been proved in fixed
median form, this theorem turns it directly into
`StrongGlobalSurfaceSubtypeLevy`. -/
theorem strongGlobalSurfaceSubtypeLevy
    {n : ℝ}
    (hFixedMedianLevy :
      ∀ {g : Metric.sphere (0 : SampleMatrix p q σ) 1 → ℝ} {K : ℝ≥0},
        LipschitzWith K g →
          ∃ Mg,
            _root_.AppendixB.IsMedian
              (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)) g Mg ∧
              ∀ {u : ℝ}, 0 < u →
                (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
                    {X | u ≤ |g X - Mg|} ≤
                  2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2)))) :
    StrongGlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n := by
  exact hFixedMedianLevy

omit [DecidableEq p] [DecidableEq q] in
/-- The strong surface Levy theorem gives the weaker existing surface API. -/
theorem StrongGlobalSurfaceSubtypeLevy.toGlobalSurfaceSubtypeLevy
    {n : ℝ}
    (h : StrongGlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n := by
  intro g K hg u hu
  rcases h hg with ⟨Mg, hMg, hTail⟩
  exact ⟨Mg, hMg, hTail hu⟩

/-- Exact remaining polar/Levy input package for the concrete spherical model.

This isolates the one genuinely geometric ingredient still external to the
repo's downstream Appendix B pipeline:

* the global Levy theorem on that canonical surface law.

Everything after this package is already wired in the concrete model. -/
structure RemainingPolarLevyInputs (n : ℝ) where
  polarLaw :
    sphericalModelMeasure (p := p) (q := q) (σ := σ) =
      surfaceModelMeasure (p := p) (q := q) (σ := σ)
  surfaceLevy :
    GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n

/-- Strong version of the remaining polar/Levy input package.

It stores the natural strong surface Levy theorem and can be downgraded to the
existing package without changing downstream code. -/
structure StrongRemainingPolarLevyInputs (n : ℝ) where
  polarLaw :
    sphericalModelMeasure (p := p) (q := q) (σ := σ) =
      surfaceModelMeasure (p := p) (q := q) (σ := σ)
  surfaceLevy :
    StrongGlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n

omit [DecidableEq p] [DecidableEq q] in
/-- Forget the stronger quantifier order and recover the existing remaining
polar/Levy package. -/
def StrongRemainingPolarLevyInputs.toRemainingPolarLevyInputs
    {n : ℝ}
    (I : StrongRemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n) :
    RemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n where
  polarLaw := I.polarLaw
  surfaceLevy :=
    StrongGlobalSurfaceSubtypeLevy.toGlobalSurfaceSubtypeLevy
      (p := p) (q := q) (σ := σ) I.surfaceLevy

omit [DecidableEq p] [DecidableEq q] in
/-- Build the remaining polar/Levy package from the single genuine remaining
surface input.  The polar-law field is the already-proved `polarLaw`; no
generic direction map or raw sphere volume is introduced here. -/
def concreteRemainingPolarLevyInputs
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hSurfaceLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    RemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n where
  polarLaw := polarLaw (p := p) (q := q) (σ := σ)
  surfaceLevy := hSurfaceLevy

omit [DecidableEq p] [DecidableEq q] in
/-- The concrete polar/Levy package has no extra polar-law input: its
`polarLaw` field is the already proved Gaussian polar-law identity. -/
theorem concreteRemainingPolarLevyInputs_polarLaw
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hSurfaceLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    (concreteRemainingPolarLevyInputs
      (p := p) (q := q) (σ := σ) hSurfaceLevy).polarLaw =
      polarLaw (p := p) (q := q) (σ := σ) := by
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- The concrete polar/Levy package stores exactly the supplied surface Levy
theorem as its only theorem-strength field. -/
theorem concreteRemainingPolarLevyInputs_surfaceLevy
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hSurfaceLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n :=
  (concreteRemainingPolarLevyInputs
    (p := p) (q := q) (σ := σ) hSurfaceLevy).surfaceLevy

omit [DecidableEq p] [DecidableEq q] in
/-- Pointwise form of the previous projection: applying the surface-Levy field
of the concrete package is just applying the supplied surface theorem. -/
theorem concreteRemainingPolarLevyInputs_surfaceLevy_apply
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hSurfaceLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n)
    {g : Metric.sphere (0 : SampleMatrix p q σ) 1 → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {u : ℝ} (hu : 0 < u) :
    (concreteRemainingPolarLevyInputs
      (p := p) (q := q) (σ := σ) hSurfaceLevy).surfaceLevy hg hu =
      hSurfaceLevy hg hu := by
  rfl

omit [DecidableEq p] [DecidableEq q] in
/-- Package the exact surface Levy theorem at the paper's pipeline exponent
into the remaining concrete polar/Levy input structure. -/
def remainingPolarLevyInputs_of_surfaceLevy
    [Nonempty p] [Nonempty q] [Nonempty σ] {cDim d : ℝ}
    (hSurface :
      GlobalSurfaceSubtypeLevy
        (p := p) (q := q) (σ := σ) (cDim * d ^ 4)) :
    RemainingPolarLevyInputs
      (p := p) (q := q) (σ := σ) (cDim * d ^ 4) :=
  concreteRemainingPolarLevyInputs
    (p := p) (q := q) (σ := σ) hSurface

omit [DecidableEq p] [DecidableEq q] in
/-- If one has the canonical surface Levy theorem at the geometric sphere
dimension, then any smaller pipeline exponent can be packaged using
`GlobalSurfaceSubtypeLevy.mono`. -/
def remainingPolarLevyInputs_of_surfaceLevyDimension
    [Nonempty p] [Nonempty q] [Nonempty σ] {cDim d : ℝ}
    (hCompare :
      cDim * d ^ 4 ≤ surfaceLevyDimension (p := p) (q := q) (σ := σ))
    (hSurfaceTop :
      GlobalSurfaceSubtypeLevy
        (p := p) (q := q) (σ := σ)
        (surfaceLevyDimension (p := p) (q := q) (σ := σ))) :
    RemainingPolarLevyInputs
      (p := p) (q := q) (σ := σ) (cDim * d ^ 4) :=
  concreteRemainingPolarLevyInputs
    (p := p) (q := q) (σ := σ)
    (GlobalSurfaceSubtypeLevy.mono
      (p := p) (q := q) (σ := σ) hCompare hSurfaceTop)

omit [DecidableEq p] [DecidableEq q] in
/-- Strong fixed-median version of `concreteRemainingPolarLevyInputs`. -/
def concreteStrongRemainingPolarLevyInputs
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hSurfaceLevy :
      StrongGlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    StrongRemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n where
  polarLaw := polarLaw (p := p) (q := q) (σ := σ)
  surfaceLevy := hSurfaceLevy

omit [DecidableEq p] [DecidableEq q] in
/-- A global Levy theorem on the sphere subtype induces the corresponding
ambient statement for observables restricted to the canonical surface law. -/
theorem globalSphericalLevy_surfaceModel_of_subtype
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hLevy : GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    GlobalSphericalLevy
      (p := p) (q := q) (σ := σ)
      (surfaceModelMeasure (p := p) (q := q) (σ := σ)) n := by
  intro g K hg u hu
  let gS : Metric.sphere (0 : SampleMatrix p q σ) 1 → ℝ :=
    fun X => g X
  have hgS : LipschitzWith K gS := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro X Y
    simpa [gS] using hg.dist_le_mul (X : SampleMatrix p q σ) Y
  rcases hLevy hgS hu with ⟨Mg, hMg, hTail⟩
  refine ⟨Mg, ?_, ?_⟩
  · rcases hMg with ⟨hLeft, hRight⟩
    constructor
    · have hmeas :
          MeasurableSet {X : SampleMatrix p q σ | g X ≤ Mg} :=
        measurableSet_le hg.continuous.measurable measurable_const
      calc
        (1 / 2 : ℝ) ≤
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
              {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | gS X ≤ Mg} :=
          hLeft
        _ =
            (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
              {X : SampleMatrix p q σ | g X ≤ Mg} := by
          unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
          rw [map_measureReal_apply continuous_subtype_val.measurable hmeas]
          rfl
    · have hmeas :
          MeasurableSet {X : SampleMatrix p q σ | Mg ≤ g X} :=
        measurableSet_le measurable_const hg.continuous.measurable
      calc
        (1 / 2 : ℝ) ≤
            (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
              {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | Mg ≤ gS X} :=
          hRight
        _ =
            (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
              {X : SampleMatrix p q σ | Mg ≤ g X} := by
          unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
          rw [map_measureReal_apply continuous_subtype_val.measurable hmeas]
          rfl
  · have hmeas :
        MeasurableSet {X : SampleMatrix p q σ | u ≤ |g X - Mg|} :=
      measurableSet_le measurable_const
        ((hg.continuous.sub continuous_const).abs.measurable)
    calc
      (surfaceModelMeasure (p := p) (q := q) (σ := σ)).real
          {X : SampleMatrix p q σ | u ≤ |g X - Mg|} =
        (sampleSurfaceProbabilityMeasure (p := p) (q := q) (σ := σ)).real
          {X : Metric.sphere (0 : SampleMatrix p q σ) 1 | u ≤ |gS X - Mg|} := by
          unfold surfaceModelMeasure sampleSurfaceProbabilityMeasureAmbient
          rw [map_measureReal_apply continuous_subtype_val.measurable hmeas]
          rfl
      _ ≤ 2 * Real.exp (-(n * u ^ 2 / (4 * K ^ 2))) := hTail

/-! ## Transport through the Gaussian polar law -/

omit [DecidableEq p] [DecidableEq q] in
/-- If the Gaussian direction law is the canonical surface law, then any global
Levy theorem for the canonical surface law transfers to the exact Gaussian
spherical model. -/
theorem globalSphericalLevy_sphericalModel_of_surface_law
    {n : ℝ}
    (hPolarLaw :
      sphericalModelMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hLevy :
      GlobalSphericalLevy
        (p := p) (q := q) (σ := σ)
        (surfaceModelMeasure (p := p) (q := q) (σ := σ)) n) :
    GlobalSphericalLevy
      (p := p) (q := q) (σ := σ)
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) n := by
  intro g K hg u hu
  simpa [hPolarLaw] using
    (hLevy (g := g) (K := K) hg (u := u) hu)

omit [DecidableEq p] [DecidableEq q] in
/-- Subtype-sphere Levy plus the Gaussian polar law gives the exact global
Levy input consumed by the localized model. -/
theorem globalSphericalLevy_sphericalModel_of_subtype_and_polar_law
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (hPolarLaw :
      sphericalModelMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hSubtypeLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    GlobalSphericalLevy
      (p := p) (q := q) (σ := σ)
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) n := by
  exact globalSphericalLevy_sphericalModel_of_surface_law
    (p := p) (q := q) (σ := σ) (n := n) hPolarLaw
    (globalSphericalLevy_surfaceModel_of_subtype
      (p := p) (q := q) (σ := σ) hSubtypeLevy)

omit [DecidableEq p] [DecidableEq q] in
/-- The remaining polar/Levy package induces the exact global spherical Levy
input consumed by the localized concrete model. -/
theorem RemainingPolarLevyInputs.globalSphericalLevy
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (I : RemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n) :
    GlobalSphericalLevy
      (p := p) (q := q) (σ := σ)
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) n := by
  exact globalSphericalLevy_sphericalModel_of_subtype_and_polar_law
    (p := p) (q := q) (σ := σ) (n := n) I.polarLaw I.surfaceLevy

omit [DecidableEq p] [DecidableEq q] in
/-- The strong remaining polar/Levy package induces the same global spherical
Levy input consumed by the localized concrete model. -/
theorem StrongRemainingPolarLevyInputs.globalSphericalLevy
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (I : StrongRemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n) :
    GlobalSphericalLevy
      (p := p) (q := q) (σ := σ)
      (sphericalModelMeasure (p := p) (q := q) (σ := σ)) n := by
  exact I.toRemainingPolarLevyInputs.globalSphericalLevy

/-! ## Surface-measure versions of the radial expectation factorization -/

omit [DecidableEq p] [DecidableEq q] in
/-- Linear radial expectation factorization, rewritten with the canonical
surface measure once the Gaussian direction law has been identified with it. -/
theorem gaussian_sampleOpNorm_expectation_factorization_surface_of_polar
    [Nonempty p] [Nonempty q] [Nonempty σ]
    (hPolarLaw :
      gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hIndep :
      gaussianRadius (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ)) :
    ∫ ω : Ω p q σ,
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (gaussianMatrix p q σ ω) ∂gaussianMeasure p q σ =
      (∫ ω : Ω p q σ,
          gaussianRadius (p := p) (q := q) (σ := σ) ω
          ∂gaussianMeasure p q σ) *
        (∫ X : SampleMatrix p q σ,
          sampleOpNorm (p := p) (q := q) (σ := σ) X
          ∂surfaceModelMeasure (p := p) (q := q) (σ := σ)) := by
  rw [gaussian_sampleOpNorm_expectation_factorization_of_indep
    (p := p) (q := q) (σ := σ) hIndep]
  rw [hPolarLaw]

omit [DecidableEq p] [DecidableEq q] in
/-- Quadratic radial expectation factorization, rewritten with the canonical
surface measure once the Gaussian direction law has been identified with it. -/
theorem gaussian_quadratic_radial_surface_factorization_of_polar
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {F : SampleMatrix p q σ → ℝ}
    (hPolarLaw :
      gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hIndep :
      gaussianRadiusSq (p := p) (q := q) (σ := σ) ⟂ᵢ[gaussianMeasure p q σ]
        gaussianDirection (p := p) (q := q) (σ := σ))
    (hF :
      AEStronglyMeasurable F
        (gaussianSphericalSampleMeasure (p := p) (q := q) (σ := σ))) :
    ∫ ω : Ω p q σ,
        gaussianMass p q σ ω *
          F (gaussianDirection (p := p) (q := q) (σ := σ) ω)
        ∂gaussianMeasure p q σ =
      (∫ ω : Ω p q σ, gaussianMass p q σ ω ∂gaussianMeasure p q σ) *
        (∫ X : SampleMatrix p q σ,
          F X ∂surfaceModelMeasure (p := p) (q := q) (σ := σ)) := by
  rw [gaussian_quadratic_radial_spherical_factorization_of_indep
    (p := p) (q := q) (σ := σ) (F := F) hIndep hF]
  rw [hPolarLaw]

/-! ## Localized Levy with canonical surface inputs -/

/-- Localized Levy on the exact spherical model, supplied by the canonical
surface-subtype Levy theorem and the Gaussian polar law. -/
theorem spherical_localized_levy_exact_good_set_with_surface_levy
    [Nonempty p] [Nonempty q] [Nonempty σ]
    {f : SampleMatrix p q σ → ℝ}
    {a b d L n t Mf : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf)
    (hPolarLaw :
      sphericalModelMeasure (p := p) (q := q) (σ := σ) =
        surfaceModelMeasure (p := p) (q := q) (σ := σ))
    (hSubtypeLevy :
      GlobalSurfaceSubtypeLevy (p := p) (q := q) (σ := σ) n) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  exact spherical_localized_levy_exact_good_set
    (p := p) (q := q) (σ := σ) (f := f)
    (a := a) (b := b) (d := d) (L := L) (n := n) (t := t) (Mf := Mf)
    ht hL hLip hMf
    (globalSphericalLevy_sphericalModel_of_subtype_and_polar_law
      (p := p) (q := q) (σ := σ) (n := n) hPolarLaw hSubtypeLevy)

/-- Localized Levy on the concrete spherical good set, using only the packaged
remaining polar/Levy inputs. -/
theorem RemainingPolarLevyInputs.localizedLevy_exact_good_set
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (I : RemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n)
    {f : SampleMatrix p q σ → ℝ}
    {a b d L t Mf : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  exact spherical_localized_levy_exact_good_set_with_surface_levy
    (p := p) (q := q) (σ := σ) (f := f)
    (a := a) (b := b) (d := d) (L := L) (n := n) (t := t) (Mf := Mf)
    ht hL hLip hMf I.polarLaw I.surfaceLevy

/-- Localized Levy on the concrete spherical good set, using the strong
remaining polar/Levy package directly. -/
theorem StrongRemainingPolarLevyInputs.localizedLevy_exact_good_set
    [Nonempty p] [Nonempty q] [Nonempty σ] {n : ℝ}
    (I : StrongRemainingPolarLevyInputs (p := p) (q := q) (σ := σ) n)
    {f : SampleMatrix p q σ → ℝ}
    {a b d L t Mf : ℝ}
    (ht : 0 < t)
    (hL : 0 ≤ L)
    (hLip :
      _root_.AppendixB.LipschitzOn
        (fun X Y : SampleMatrix p q σ => dist X Y)
        (sphericalOperatorNormGoodSet (p := p) (q := q) (σ := σ) a b d)
        f L)
    (hMf :
      _root_.AppendixB.IsMedian
        (sphericalModelMeasure (p := p) (q := q) (σ := σ)) f Mf) :
    (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
        {X | t ≤ |f X - Mf|} ≤
      2 *
          (sphericalModelMeasure (p := p) (q := q) (σ := σ)).real
            (sphericalOperatorNormGoodSet
              (p := p) (q := q) (σ := σ) a b d)ᶜ +
        4 * Real.exp (-(n * t ^ 2 / (16 * L ^ 2))) := by
  exact I.toRemainingPolarLevyInputs.localizedLevy_exact_good_set
    (p := p) (q := q) (σ := σ) (f := f)
    (a := a) (b := b) (d := d) (L := L) (t := t) (Mf := Mf)
    ht hL hLip hMf

end AppendixB
end PptFactorization
