import PptFactorization.AppendixBSurfaceMeasure

/-!
Aristotle handoff for the upper-bound geometric core.

Target: prove the no-input real-sphere isoperimetric supplier
`PptFactorization.AppendixB.sphere_caps_minimize_neighborhoods` (alias
`FullSphericalIsoperimetry`).

Protected files: do not edit `PptFactorization/AppendixBSpikeLowerBound.lean`.

Allowed imports/context: use existing local lemmas from
`PptFactorization/AppendixBSurfaceMeasure`,
`PptFactorization/AppendixBSphericalConcentration`, and mathlib.  Do not add
axioms, `opaque`, `unsafe`, or new theorem parameters.

## Plain math (self-contained)

On the unit sphere `S^{n-1} ⊂ ℝ^n`, with normalized surface probability μ,
for every measurable A ⊆ S^{n-1} with μ(A) ≥ 1/2 and every r ≥ 0, the
geodesic r-neighbourhood of A has complement of μ-mass at most
exp(−((n−1) r²)/2).

Equivalently: spherical caps minimize geodesic neighbourhoods among sets of
given surface measure (Lévy isoperimetry); the project consumes only this
half-mass Gaussian tail consequence.

## Metric bookkeeping (already closed locally — transport only)

* Geodesic distance uses chord–arc comparison
  (`finRealSphereGeodesicDistance`, `finRealSphere_dist_le_geodesicDistance`).
* Geodesic thickenings sit inside Euclidean/chord thickenings
  (`finRealSphereGeodesicThickening_subset_metricThickening`).
* Ambient Euclidean thickenings compare to geodesic complements in measure
  (`finRealSurfaceProbabilityMeasureAmbient_compl_ambientThickening_image_le_geodesic`).
* Closed hemispheres have surface mass 1/2
  (`finRealSurfaceProbabilityMeasure_closedHemisphere_half`).
* Hemisphere cap-tail is already derived *from* the bound, not vice versa
  (`finRealSurfaceProbabilityMeasure_closedHemisphere_geodesicCapTail_le_of_fullSphericalIsoperimetry`).

## Downstream transport (already proved — not part of this target)

Once `sphere_caps_minimize_neighborhoods` is available, the project already
closes:

* `globalSurfaceSubtypeLevy_of_fullSphericalIsoperimetry`
* `sharpSphericalIsoperimetry_sphericalModelMeasure_of_fullSphericalIsoperimetry`
* `upper_hIso_concreteModel_pointwise_of_fullSphericalIsoperimetry`
* moment mean-tail and exponential packaging in `AppendixBUpperBoundClosure.lean`.

## Mathlib audit (2026-05-22)

No mathlib lemma was found matching this geodesic half-measure Gaussian tail
on `FinRealSphere n` with `finRealSurfaceProbabilityMeasure`.  Mathlib has
sphere geometry (`Mathlib.Geometry.Manifold.Instances.Sphere`), Euclidean
spheres, and planar isoperimetry formalizations elsewhere, but not Lévy
concentration / spherical isoperimetric inequality in the required form.

Expected proof route (classical, not yet formalized here): Steiner
symmetrization or spherical cap comparison showing caps minimize geodesic
neighbourhood mass, then a Gaussian isoperimetric functional inequality
(Bobkov–Ledoux type) yielding the stated tail.

PROVIDED TARGET:
The proposition below is the exact no-input target.  It is intentionally a
definition, not a theorem with a placeholder proof: this handoff file must not
look like an audited supplier until the geometric theorem has actually been
proved.
-/

namespace PptFactorization.AppendixB

/-- Exact target proposition for the no-input real-sphere isoperimetry
supplier.  A proof term of this proposition, not this definition itself, closes
`FullSphericalIsoperimetry`. -/
abbrev sphere_caps_minimize_neighborhoods_noInput_target : Prop :=
  sphere_caps_minimize_neighborhoods

/-- The handoff target is exactly the geometric input consumed downstream. -/
theorem sphere_caps_minimize_neighborhoods_noInput_target_iff_FullSphericalIsoperimetry :
    sphere_caps_minimize_neighborhoods_noInput_target ↔ FullSphericalIsoperimetry := by
  rfl

/-- A proof of the handoff target closes the downstream geometric input. -/
theorem FullSphericalIsoperimetry_of_sphere_caps_minimize_neighborhoods_noInput_target
    (h : sphere_caps_minimize_neighborhoods_noInput_target) :
    FullSphericalIsoperimetry :=
  (sphere_caps_minimize_neighborhoods_noInput_target_iff_FullSphericalIsoperimetry).1 h

/-- Conversely, the downstream geometric input is the exact handoff target. -/
theorem sphere_caps_minimize_neighborhoods_noInput_target_of_FullSphericalIsoperimetry
    (h : FullSphericalIsoperimetry) :
    sphere_caps_minimize_neighborhoods_noInput_target :=
  (sphere_caps_minimize_neighborhoods_noInput_target_iff_FullSphericalIsoperimetry).2 h

/-- The lower-camel-case compatibility alias is also the same target. -/
theorem sphere_caps_minimize_neighborhoods_noInput_target_iff_fullSphericalIsoperimetry :
    sphere_caps_minimize_neighborhoods_noInput_target ↔ fullSphericalIsoperimetry := by
  rfl

end PptFactorization.AppendixB
