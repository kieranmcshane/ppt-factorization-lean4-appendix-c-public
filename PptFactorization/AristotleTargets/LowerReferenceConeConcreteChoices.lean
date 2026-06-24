import PptFactorization.AppendixBLowerBoundClosure

/-!
Aristotle handoff for the lower-bound closure.

Target: close the lower pipeline input `hReference` by proving the reference
projective cone-coordinate formula for the concrete ambient type
`BipIndex (Fin d) (Fin d)`, eventually in `d`.

Protected file: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.

Allowed inputs/context: use existing local lemmas from
`PptFactorization.AppendixBLowerBoundClosure` and its imports, plus mathlib.
Do not add axioms, `opaque`, `unsafe`, new theorem parameters, or weaken the
statement.

Known relevant definitions/lemmas:
* `AppendixB.SurfaceReferenceProjectiveCapConeCoordinateFormula`
* `AppendixB.SurfaceProjectiveCapConeCoordinateFormula.of_reference`
* `AppendixB.hermitianBlockMass_map_surfaceMeasureAmbient_eq_beta`
* `AppendixB.betaMeasure_one_nat_sub_projectiveOverlapKernelTail`
* `AppendixB.projectiveConeCoordinateRatio_eq_pow`
* `AppendixB.surfaceMeasure`
* `AppendixB.coordinateUnitVector`
* `AppendixB.norm_coordinateUnitVector`

PROVIDED SOLUTION:
Prove the statement through the exact spherical block-mass law, not through a
raw cone-volume integral.  In the canonical type `PUnit ⊕ κ`, the projective
overlap with the singleton coordinate is exactly the left Hermitian block mass.
The closed Gaussian/spherical disintegration theorem identifies that block
mass with a `Beta(1, card κ)` law, whose upper tail gives the projective cap
probability.  Then transport the result along a finite index equivalence from
`PUnit ⊕ {j // j ≠ i₀}` to the concrete coordinate type
`BipIndex (Fin d) (Fin d)`.  Preserve the theorem statements exactly.
-/
namespace AppendixB

open MeasureTheory
open PptFactorization.RandomMatrixModel
open Filter
open scoped ENNReal Topology

/-!
Pointwise reduction.

The eventual lower input is only bookkeeping once the following fixed-dimension
reference formula is known.  The proof below uses the already closed
Gaussian/spherical block-mass Beta law as the exact disintegration input.  This
keeps the hReference closure on the same project-axiom-free probability spine
as the deleted-column product decomposition, and avoids introducing a separate
raw cone-volume integral.
-/

/-- On the singleton-left block `PUnit ⊕ κ`, the squared overlap with the
distinguished coordinate is exactly the Hermitian left-block mass.

This is the algebraic bridge that lets the already closed spherical block-mass
Beta law supply the reference cap computation in the canonical
`one coordinate + complement` model. -/
theorem lower_projectiveOverlapSq_coordinateUnitVector_sumPUnit_eq_hermitianBlockMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (x : Metric.sphere (0 : EuclideanSpace ℂ (Sum PUnit κ)) 1) :
    projectiveOverlapSq (ι := Sum PUnit κ)
        (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit)) x =
      hermitianBlockMass (ι := PUnit) (κ := κ)
        (x : EuclideanSpace ℂ (Sum PUnit κ)) := by
  unfold projectiveOverlapSq coordinateUnitVector
  have hinner :
      inner ℂ (WithLp.toLp 2 (Pi.single (Sum.inl PUnit.unit) (1 : ℂ)))
          (x : EuclideanSpace ℂ (Sum PUnit κ)) =
        (x : EuclideanSpace ℂ (Sum PUnit κ)).ofLp (Sum.inl PUnit.unit) := by
    rw [PiLp.inner_apply]
    rw [Finset.sum_eq_single (Sum.inl PUnit.unit)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hnot
      simp at hnot
  rw [hinner]
  unfold hermitianBlockMass hermitianBlockLeft
  rw [PiLp.norm_sq_eq_of_L2]
  simp

/-- Exact reference projective-cap probability in the canonical
`one coordinate + complement` model.

This proof routes through the closed block-mass law
`hermitianBlockMass_map_surfaceMeasureAmbient_eq_beta` and the already proved
`Beta(1,N-1)` upper-tail identity. -/
theorem lower_projectiveCapProbability_sumPUnit_coordinateUnitVector_eq_pow
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [SFinite
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum PUnit κ))).toSphere)]
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    projectiveCapProbability (ι := Sum PUnit κ) (surfaceMeasure (Sum PUnit κ))
        (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit)) r =
      r ^ (2 * (Fintype.card (Sum PUnit κ) - 1)) := by
  classical
  let e : EuclideanSpace ℂ (Sum PUnit κ) :=
    coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit)
  let s : Set (EuclideanSpace ℂ (Sum PUnit κ)) :=
    (hermitianBlockMass (ι := PUnit) (κ := κ)) ⁻¹' Set.Ici (1 - r ^ 2)
  have hs : MeasurableSet s := by
    dsimp [s]
    exact (measurable_hermitianBlockMass (ι := PUnit) (κ := κ))
      measurableSet_Ici
  have hpre :
      (Subtype.val :
          Metric.sphere (0 : EuclideanSpace ℂ (Sum PUnit κ)) 1 →
            EuclideanSpace ℂ (Sum PUnit κ)) ⁻¹' s =
        projectiveCapSet (ι := Sum PUnit κ) e r := by
    ext x
    change
      1 - r ^ 2 ≤
          hermitianBlockMass (ι := PUnit) (κ := κ)
            (x : EuclideanSpace ℂ (Sum PUnit κ)) ↔
        1 - r ^ 2 ≤
          ‖inner ℂ e (x : EuclideanSpace ℂ (Sum PUnit κ))‖ ^ 2
    rw [←
      lower_projectiveOverlapSq_coordinateUnitVector_sumPUnit_eq_hermitianBlockMass
        (κ := κ) x]
    rfl
  have hcap_ambient :
      projectiveCapProbability (ι := Sum PUnit κ)
          (surfaceMeasure (Sum PUnit κ)) e r =
        (surfaceMeasureAmbient (Sum PUnit κ)).real s := by
    unfold projectiveCapProbability surfaceMeasureAmbient
    rw [map_measureReal_apply measurable_subtype_coe hs]
    exact congrArg (fun t => (surfaceMeasure (Sum PUnit κ)).real t) hpre.symm
  have hmap :=
    hermitianBlockMass_map_surfaceMeasureAmbient_eq_beta
      (ι := PUnit) (κ := κ)
  have hbeta :
      (surfaceMeasureAmbient (Sum PUnit κ)).real s =
        (hermitianBlockMassBetaMeasure (ι := PUnit) (κ := κ)).real
          (Set.Ici (1 - r ^ 2)) := by
    calc
      (surfaceMeasureAmbient (Sum PUnit κ)).real s =
          (Measure.map (hermitianBlockMass (ι := PUnit) (κ := κ))
            (surfaceMeasureAmbient (Sum PUnit κ))).real
              (Set.Ici (1 - r ^ 2)) := by
            rw [map_measureReal_apply
              (measurable_hermitianBlockMass (ι := PUnit) (κ := κ))
              measurableSet_Ici]
      _ =
          (hermitianBlockMassBetaMeasure (ι := PUnit) (κ := κ)).real
            (Set.Ici (1 - r ^ 2)) := by
            rw [hmap]
  have hN : 2 ≤ Fintype.card (Sum PUnit κ) := by
    have hκ : 1 ≤ Fintype.card κ :=
      Nat.succ_le_of_lt Fintype.card_pos
    simpa [Fintype.card_sum, Nat.add_comm] using Nat.succ_le_succ hκ
  by_cases hrpos : 0 < r
  · have htail :=
      (betaMeasure_one_nat_sub_projectiveOverlapKernelTail hN).tail_eq
        hrpos (le_of_lt hr1)
    calc
      projectiveCapProbability (ι := Sum PUnit κ)
          (surfaceMeasure (Sum PUnit κ)) e r =
          (hermitianBlockMassBetaMeasure (ι := PUnit) (κ := κ)).real
            (Set.Ici (1 - r ^ 2)) := by
            rw [hcap_ambient, hbeta]
      _ = r ^ (2 * (Fintype.card (Sum PUnit κ) - 1)) := by
            simpa [hermitianBlockMassBetaMeasure, projectiveCapKernel,
              Fintype.card_sum] using htail
  · have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) hr0
    subst r
    have htail0 :=
      betaMeasure_one_nat_sub_real_Ici_of_one_le hN
        (by norm_num : (1 : ℝ) ≤ 1 - (0 : ℝ) ^ 2)
    calc
      projectiveCapProbability (ι := Sum PUnit κ)
          (surfaceMeasure (Sum PUnit κ)) e (0 : ℝ) =
          (hermitianBlockMassBetaMeasure (ι := PUnit) (κ := κ)).real
            (Set.Ici (1 - (0 : ℝ) ^ 2)) := by
            rw [hcap_ambient, hbeta]
      _ = 0 := by
            simpa [hermitianBlockMassBetaMeasure, Fintype.card_sum] using htail0
      _ = (0 : ℝ) ^ (2 * (Fintype.card (Sum PUnit κ) - 1)) := by
            symm
            have hpos :
                2 * (Fintype.card (Sum PUnit κ) - 1) ≠ 0 := by
              omega
            exact zero_pow hpos

/-- The reference cone-coordinate formula is closed for the canonical
singleton-coordinate model `PUnit ⊕ κ`.

The remaining `hReference` task is therefore no longer the scalar cap law in
this canonical model; it is the transport from an arbitrary concrete coordinate
type, such as `BipIndex (Fin d) (Fin d)`, to this singleton-plus-complement
decomposition. -/
theorem lower_surfaceReferenceProjectiveCapConeCoordinateFormula_sumPUnit
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [SFinite
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum PUnit κ))).toSphere)] :
    SurfaceReferenceProjectiveCapConeCoordinateFormula
      (Sum PUnit κ) (Sum.inl PUnit.unit) := by
  intro r hr0 hr1
  rw [lower_projectiveCapProbability_sumPUnit_coordinateUnitVector_eq_pow
    (κ := κ) hr0 hr1]
  rw [projectiveConeCoordinateRatio_eq_pow
    (Fintype.card (Sum PUnit κ) - 1) hr0 hr1]

/-- Probability-normalized surface measure is transported by a finite index
equivalence on complex Euclidean coordinate spaces. -/
theorem lower_surfaceMeasure_map_piLpCongrLeft
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere)]
    (e : ι ≃ κ) :
    Measure.map
        (Subtype.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
          (fun _ hx => by simpa using hx))
        (surfaceMeasure ι) =
      surfaceMeasure κ := by
  let V : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let U : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ κ :=
    IsometryEquiv.toRealLinearIsometryEquivOfMapZero V.toIsometryEquiv
      (by simp : V.toIsometryEquiv 0 = 0)
  have hmapU :
      Measure.map U
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)) =
        (1 : ℝ≥0∞) •
          (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)) := by
    simpa using U.measurePreserving.map_eq
  have hfinι :
      IsFiniteMeasure
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere) := ⟨by
    have hball_lt :
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι))
            (Metric.ball (0 : EuclideanSpace ℂ ι) 1) < ∞ := by
      exact lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : EuclideanSpace ℂ ι) 1).measure_lt_top)
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_lt_top (by simp) hball_lt⟩
  have hfinκ :
      IsFiniteMeasure
        ((MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)).toSphere) := ⟨by
    have hball_lt :
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ))
            (Metric.ball (0 : EuclideanSpace ℂ κ) 1) < ∞ := by
      exact lt_of_le_of_lt
        (measure_mono Metric.ball_subset_closedBall)
        ((isCompact_closedBall (0 : EuclideanSpace ℂ κ) 1).measure_lt_top)
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_lt_top (by simp) hball_lt⟩
  have h :=
    PptFactorization.AppendixB.map_toFinite_toSphere_linearIsometryEquiv_of_map_eq_smul
      (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)))
      (ν := (MeasureTheory.volume : Measure (EuclideanSpace ℂ κ)))
      (U := U) (c := (1 : ℝ≥0∞)) (by simp) (by simp) hmapU
  simpa [surfaceMeasure, V, U] using h

/-- The index-equivalence map sends the singleton coordinate vector to the
target coordinate vector when the equivalence sends `Sum.inl PUnit.unit` to
that coordinate. -/
theorem lower_coordinateUnitVector_map_sumPUnit_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (eidx : Sum PUnit κ ≃ ι) (i₀ : ι)
    (hi₀ : eidx (Sum.inl PUnit.unit) = i₀) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eidx)
        (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit)) =
      coordinateUnitVector (ι := ι) i₀ := by
  ext j
  by_cases hj : j = i₀
  · subst j
    have hsymm : eidx.symm i₀ = Sum.inl PUnit.unit := by
      rw [← hi₀]
      simp
    simp [coordinateUnitVector, LinearIsometryEquiv.piLpCongrLeft]
    rw [hsymm]
    simp
  · have hsymm_ne : eidx.symm j ≠ Sum.inl PUnit.unit := by
      intro h
      apply hj
      calc
        j = eidx (eidx.symm j) := by simp
        _ = eidx (Sum.inl PUnit.unit) := by rw [h]
        _ = i₀ := hi₀
    simp [coordinateUnitVector, LinearIsometryEquiv.piLpCongrLeft, hj,
      hsymm_ne]

/-- Pulling back the target-coordinate projective cap along a finite index
equivalence gives the canonical singleton-coordinate projective cap. -/
theorem lower_projectiveCapSet_preimage_sumPUnit_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (eidx : Sum PUnit κ ≃ ι) (i₀ : ι)
    (hi₀ : eidx (Sum.inl PUnit.unit) = i₀)
    (r : ℝ) :
    (Subtype.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eidx)
        (fun _ hx => by simpa using hx)) ⁻¹'
      projectiveCapSet (ι := ι) (coordinateUnitVector (ι := ι) i₀) r =
    projectiveCapSet (ι := Sum PUnit κ)
      (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit)) r := by
  ext u
  simp [projectiveCapSet]
  let V : EuclideanSpace ℂ (Sum PUnit κ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eidx
  have hVe :
      V (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit)) =
        coordinateUnitVector (ι := ι) i₀ :=
    lower_coordinateUnitVector_map_sumPUnit_equiv (κ := κ) eidx i₀ hi₀
  have hinner :
      inner ℂ (coordinateUnitVector (ι := ι) i₀)
          (V (u : EuclideanSpace ℂ (Sum PUnit κ))) =
        inner ℂ
          (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit))
          (u : EuclideanSpace ℂ (Sum PUnit κ)) := by
    rw [← hVe]
    simp
  change
    1 ≤
        ‖inner ℂ (coordinateUnitVector (ι := ι) i₀)
          (V (u : EuclideanSpace ℂ (Sum PUnit κ)))‖ ^ 2 + r ^ 2 ↔
      1 ≤
        ‖inner ℂ
          (coordinateUnitVector (ι := Sum PUnit κ) (Sum.inl PUnit.unit))
          (u : EuclideanSpace ℂ (Sum PUnit κ))‖ ^ 2 + r ^ 2
  rw [hinner]

/-- Transport the canonical singleton-coordinate reference formula along a
finite index equivalence. -/
theorem lower_surfaceReferenceProjectiveCapConeCoordinateFormula_of_sumPUnit_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    [SFinite
      ((MeasureTheory.volume : Measure (EuclideanSpace ℂ (Sum PUnit.{1} κ))).toSphere)]
    (eidx : Sum PUnit.{1} κ ≃ ι) (i₀ : ι)
    (hi₀ : eidx (Sum.inl PUnit.unit) = i₀) :
    SurfaceReferenceProjectiveCapConeCoordinateFormula ι i₀ := by
  intro r hr0 hr1
  let V : EuclideanSpace ℂ (Sum PUnit.{1} κ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eidx
  let S : Metric.sphere (0 : EuclideanSpace ℂ (Sum PUnit.{1} κ)) 1 →
      Metric.sphere (0 : EuclideanSpace ℂ ι) 1 :=
    Subtype.map V (fun _ hx => by simpa using hx)
  have hS_meas : Measurable S :=
    V.continuous.subtype_map (fun _ hx => by simpa using hx) |>.measurable
  have hmap :
      Measure.map S (surfaceMeasure (Sum PUnit.{1} κ)) = surfaceMeasure ι := by
    simpa [S, V] using
      lower_surfaceMeasure_map_piLpCongrLeft
        (ι := Sum PUnit.{1} κ) (κ := ι) eidx
  have hpre :=
    lower_projectiveCapSet_preimage_sumPUnit_equiv
      (κ := κ) eidx i₀ hi₀ r
  have hprob :
      projectiveCapProbability (ι := ι) (surfaceMeasure ι)
          (coordinateUnitVector (ι := ι) i₀) r =
        projectiveCapProbability (ι := Sum PUnit.{1} κ)
          (surfaceMeasure (Sum PUnit.{1} κ))
          (coordinateUnitVector (ι := Sum PUnit.{1} κ)
            (Sum.inl PUnit.unit)) r := by
    unfold projectiveCapProbability
    calc
      (surfaceMeasure ι).real
          (projectiveCapSet (ι := ι)
            (coordinateUnitVector (ι := ι) i₀) r) =
          (Measure.map S (surfaceMeasure (Sum PUnit.{1} κ))).real
            (projectiveCapSet (ι := ι)
              (coordinateUnitVector (ι := ι) i₀) r) := by
          rw [hmap]
      _ = (surfaceMeasure (Sum PUnit.{1} κ)).real
            (S ⁻¹' projectiveCapSet (ι := ι)
              (coordinateUnitVector (ι := ι) i₀) r) := by
          rw [map_measureReal_apply hS_meas
            (measurableSet_projectiveCapSet (ι := ι)
              (coordinateUnitVector (ι := ι) i₀) r)]
      _ = (surfaceMeasure (Sum PUnit.{1} κ)).real
            (projectiveCapSet (ι := Sum PUnit.{1} κ)
              (coordinateUnitVector (ι := Sum PUnit.{1} κ)
                (Sum.inl PUnit.unit)) r) := by
          simpa [S, V] using
            congrArg (fun t => (surfaceMeasure (Sum PUnit.{1} κ)).real t)
              hpre
  rw [hprob]
  have hcard : Fintype.card (Sum PUnit.{1} κ) = Fintype.card ι :=
    Fintype.card_congr eidx
  calc
    projectiveCapProbability (ι := Sum PUnit.{1} κ)
        (surfaceMeasure (Sum PUnit.{1} κ))
        (coordinateUnitVector (ι := Sum PUnit.{1} κ)
          (Sum.inl PUnit.unit)) r =
      projectiveConeCoordinateRatio (Fintype.card (Sum PUnit.{1} κ) - 1) r := by
        exact lower_surfaceReferenceProjectiveCapConeCoordinateFormula_sumPUnit
          (κ := κ) (r := r) hr0 hr1
    _ = projectiveConeCoordinateRatio (Fintype.card ι - 1) r := by
        rw [hcard]

/-- Split a finite type into a distinguished coordinate and its complement,
with the distinguished coordinate represented by `PUnit`. -/
noncomputable def lower_sumPUnitComplementEquiv
    {ι : Type*} [DecidableEq ι] (i₀ : ι) :
    Sum PUnit.{1} {j : ι // j ≠ i₀} ≃ ι := by
  let left : PUnit.{1} ≃ {j : ι // j = i₀} :=
    { toFun := fun _ => ⟨i₀, rfl⟩
      invFun := fun _ => PUnit.unit
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; ext; exact x.2.symm }
  exact (Equiv.sumCongr left (Equiv.refl {j : ι // j ≠ i₀})).trans
    (Equiv.sumCompl (fun j : ι => j = i₀))

@[simp] theorem lower_sumPUnitComplementEquiv_apply_inl
    {ι : Type*} [DecidableEq ι] (i₀ : ι) :
    lower_sumPUnitComplementEquiv i₀ (Sum.inl PUnit.unit) = i₀ := by
  simp [lower_sumPUnitComplementEquiv]

/-- Reference cone-coordinate formula from a nonempty complement of the
distinguished coordinate. -/
theorem lower_surfaceReferenceProjectiveCapConeCoordinateFormula_of_nonempty_complement
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [SFinite ((MeasureTheory.volume : Measure (EuclideanSpace ℂ ι)).toSphere)]
    (i₀ : ι) [Nonempty {j : ι // j ≠ i₀}] :
    SurfaceReferenceProjectiveCapConeCoordinateFormula ι i₀ := by
  exact
    lower_surfaceReferenceProjectiveCapConeCoordinateFormula_of_sumPUnit_equiv
      (κ := {j : ι // j ≠ i₀})
      (lower_sumPUnitComplementEquiv i₀) i₀
      (lower_sumPUnitComplementEquiv_apply_inl i₀)

theorem lower_bipIndex_fin_complement_nonempty
    {d : ℕ} (hd : 1 < d) (i₀ : BipIndex (Fin d) (Fin d)) :
    Nonempty {j : BipIndex (Fin d) (Fin d) // j ≠ i₀} := by
  have hcard : 1 < Fintype.card (BipIndex (Fin d) (Fin d)) := by
    simp [BipIndex]
    nlinarith
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i₀
  exact ⟨⟨j, hj⟩⟩

theorem lower_surfaceReferenceProjectiveCapConeCoordinateFormula_pointwise
    {d : ℕ} (hd : 1 < d) (i₀ : BipIndex (Fin d) (Fin d)) :
    SurfaceReferenceProjectiveCapConeCoordinateFormula
      (BipIndex (Fin d) (Fin d)) i₀ := by
  haveI : Nonempty (Fin d) := ⟨0, by omega⟩
  haveI : Nonempty (BipIndex (Fin d) (Fin d)) := ⟨i₀⟩
  haveI : Nonempty {j : BipIndex (Fin d) (Fin d) // j ≠ i₀} :=
    lower_bipIndex_fin_complement_nonempty hd i₀
  change ∀ {r : ℝ}, 0 ≤ r → r < 1 →
    projectiveCapProbability (ι := BipIndex (Fin d) (Fin d))
        (surfaceMeasure (BipIndex (Fin d) (Fin d)))
        (coordinateUnitVector (ι := BipIndex (Fin d) (Fin d)) i₀) r =
      projectiveConeCoordinateRatio
        (Fintype.card (BipIndex (Fin d) (Fin d)) - 1) r
  exact lower_surfaceReferenceProjectiveCapConeCoordinateFormula_of_nonempty_complement i₀

theorem lower_referenceCone_BipIndex_Fin_eventually_concreteChoices :
    ∀ᶠ d in atTop,
      ∀ i₀ : BipIndex (Fin d) (Fin d),
        SurfaceReferenceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)) i₀ := by
  filter_upwards [eventually_gt_atTop 1] with d hd i₀
  exact lower_surfaceReferenceProjectiveCapConeCoordinateFormula_pointwise hd i₀

/-- Closed lower reference-cone input for the concrete bipartite coordinate
type. -/
theorem lower_referenceCone_BipIndex_Fin_eventually_concreteChoices_closed :
    ∀ᶠ d in atTop,
      ∀ i₀ : BipIndex (Fin d) (Fin d),
        SurfaceReferenceProjectiveCapConeCoordinateFormula
          (BipIndex (Fin d) (Fin d)) i₀ :=
  lower_referenceCone_BipIndex_Fin_eventually_concreteChoices

end AppendixB
