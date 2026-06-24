import PptFactorization.HighProbabilityBounds

/-!
# Bridge from Gaussian Wishart bounds to Appendix B normalized inputs

This file is downstream of both `AppendixB` and `HighProbabilityBounds`.
It turns the concrete Gaussian Wishart estimates into the normalized
operator-norm good-set input used in Appendix B.

The deterministic bridge is the exact radial identity

`rho(G) = (s / T) • wishart(G)`,

and the same identity after partial transpose, where
`T = ‖G‖₂²` and `s` is the number of sample columns.  Combining this with the
mass lower tail and the two Wishart operator-norm tails gives the normalized
good-set estimate by a three-event union bound.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal

noncomputable section

namespace PptFactorization
namespace HighProbabilityBounds

open RandomMatrixModel GaussianModel HighDimensionalProbability

variable {p q σ : Type*}
variable [Fintype p] [Fintype q] [Fintype σ]
variable [DecidableEq p] [DecidableEq q]

/-! ## Appendix-facing normalized operator-norm events -/

/-- The squared form of the Appendix B sample operator-norm event.

In the paper notation, `D = d^2`; the bound `‖XX*‖∞ ≤ M / D` is equivalent to
`‖X‖∞ ≤ sqrt M / d`. -/
def normalizedDensityOpNormEvent (M D : ℝ) : Set (Ω p q σ) :=
  {ω | opNorm (rho (gaussianMatrix p q σ ω)) ≤ M / D}

/-- The Appendix B partial-transpose normalized operator-norm event. -/
def normalizedGammaDensityOpNormEvent (M D : ℝ) : Set (Ω p q σ) :=
  {ω | opNorm (rhoGamma (gaussianMatrix p q σ ω)) ≤ M / D}

/-- The normalized operator-norm input event used by Appendix B:
both the density and the partially transposed density have operator norm at
scale `M / D`. -/
def normalizedOperatorNormInputEvent (M D : ℝ) : Set (Ω p q σ) :=
  normalizedDensityOpNormEvent (p := p) (q := q) (σ := σ) M D ∩
    normalizedGammaDensityOpNormEvent (p := p) (q := q) (σ := σ) M D

/-- Paper-shaped normalized sample operator-norm event
`Ω₁ = {‖X‖∞ ≤ a / d}` for `X = G / ‖G‖₂`. -/
def normalizedSampleOpNormEvent (a d : ℝ) : Set (Ω p q σ) :=
  {ω | sampleOpNorm (p := p) (q := q) (σ := σ)
      (normalizedSample (gaussianMatrix p q σ ω)) ≤ a / d}

/-- Paper-shaped normalized partial-transpose event
`Ω₂ = {‖ρ_X^Γ‖∞ ≤ b / d²}`. -/
def normalizedRhoGammaOpNormEvent (b d : ℝ) : Set (Ω p q σ) :=
  {ω | opNorm (rhoGamma (gaussianMatrix p q σ ω)) ≤ b / d ^ 2}

@[simp] theorem normalizedOperatorNormInputEvent_eq_densityGoodEvent
    (M D : ℝ) :
    normalizedOperatorNormInputEvent (p := p) (q := q) (σ := σ) M D =
      densityGoodEvent (p := p) (q := q) (σ := σ) M D := by
  ext ω
  simp [normalizedOperatorNormInputEvent, normalizedDensityOpNormEvent,
    normalizedGammaDensityOpNormEvent, densityGoodEvent, goodSet, goodEvent]

/-- The density operator norm is the square of the sample operator norm. -/
theorem opNorm_densityMatrix_eq_sampleOpNorm_sq
    (X : SampleMatrix p q σ) :
    opNorm (densityMatrix X) =
      sampleOpNorm (p := p) (q := q) (σ := σ) X ^ 2 := by
  classical
  open scoped Matrix.Norms.L2Operator in
  have hs :
      sampleOpNorm (p := p) (q := q) (σ := σ) X =
        @norm (SampleMatrix p q σ)
          (@NormedAddCommGroup.toNorm _ <|
            Matrix.instL2OpNormedAddCommGroup
              (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q) (n := σ)) X := by
    simpa [sampleOpNorm] using (Eq.symm (Matrix.l2_opNorm_def (A := X)))
  have hρ :
      opNorm (densityMatrix X) =
        @norm (BipMatrix p q)
          (@NormedAddCommGroup.toNorm _ <|
            Matrix.instL2OpNormedAddCommGroup
              (𝕜 := ℂ) (m := RandomMatrixModel.BipIndex p q)
              (n := RandomMatrixModel.BipIndex p q))
          (X * Xᴴ) := by
    simpa [opNorm, densityMatrix] using
      (Eq.symm (Matrix.cstar_norm_def (A := X * Xᴴ)))
  calc
    opNorm (densityMatrix X) = _ := hρ
    _ = ‖Xᴴ‖ * ‖Xᴴ‖ := by
      simpa using (Matrix.l2_opNorm_conjTranspose_mul_self (A := Xᴴ))
    _ = ‖X‖ * ‖X‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
    _ = sampleOpNorm (p := p) (q := q) (σ := σ) X ^ 2 := by
      rw [hs]
      ring

/-- Paper event `Ω₁` is exactly the squared-density event with `M = a²`
and `D = d²`. -/
theorem normalizedSampleOpNormEvent_eq_normalizedDensityOpNormEvent
    {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d =
      normalizedDensityOpNormEvent (p := p) (q := q) (σ := σ) (a ^ 2) (d ^ 2) := by
  ext ω
  have hsq :
      opNorm (rho (gaussianMatrix p q σ ω)) =
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) ^ 2 := by
    simpa [rho] using
      opNorm_densityMatrix_eq_sampleOpNorm_sq
        (p := p) (q := q) (σ := σ)
        (normalizedSample (gaussianMatrix p q σ ω))
  have hdnonneg : 0 ≤ d := hd.le
  constructor <;> intro h
  · have hsample :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) ≤ a / d := by
        simpa [normalizedSampleOpNormEvent] using h
    have hadiv_nonneg : 0 ≤ a / d := by
      exact div_nonneg ha hd.le
    have hnonneg :
        0 ≤ sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) := by
      unfold sampleOpNorm
      positivity
    have hsq' :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) ^ 2 ≤ (a / d) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg hnonneg, abs_of_nonneg hadiv_nonneg]
      exact hsample
    have hright : (a / d) ^ 2 = a ^ 2 / d ^ 2 := by ring
    have hρ :
        opNorm (rho (gaussianMatrix p q σ ω)) ≤ a ^ 2 / d ^ 2 := by
      calc
        opNorm (rho (gaussianMatrix p q σ ω))
            = sampleOpNorm (p := p) (q := q) (σ := σ)
                (normalizedSample (gaussianMatrix p q σ ω)) ^ 2 := hsq
        _ ≤ (a / d) ^ 2 := hsq'
        _ = a ^ 2 / d ^ 2 := by rw [hright]
    simpa [normalizedDensityOpNormEvent] using hρ
  · have hρ :
        opNorm (rho (gaussianMatrix p q σ ω)) ≤ a ^ 2 / d ^ 2 := by
        simpa [normalizedDensityOpNormEvent] using h
    have hnonneg :
        0 ≤ sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) := by
      unfold sampleOpNorm
      positivity
    have hadiv_nonneg : 0 ≤ a / d := by
      exact div_nonneg ha hd.le
    have hright : (a / d) ^ 2 = a ^ 2 / d ^ 2 := by ring
    have hsqBound :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) ^ 2 ≤ a ^ 2 / d ^ 2 := by
      rw [hsq] at hρ
      exact hρ
    have hroot :
        |sampleOpNorm (p := p) (q := q) (σ := σ)
            (normalizedSample (gaussianMatrix p q σ ω))| ≤ |a / d| := by
      apply sq_le_sq.mp
      simpa [hright] using hsqBound
    have hsample :
        sampleOpNorm (p := p) (q := q) (σ := σ)
          (normalizedSample (gaussianMatrix p q σ ω)) ≤ a / d := by
      rw [abs_of_nonneg hnonneg, abs_of_nonneg hadiv_nonneg] at hroot
      exact hroot
    simpa [normalizedSampleOpNormEvent] using hsample

@[simp] theorem normalizedRhoGammaOpNormEvent_eq_normalizedGammaDensityOpNormEvent
    (b d : ℝ) :
    normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d =
      normalizedGammaDensityOpNormEvent (p := p) (q := q) (σ := σ) b (d ^ 2) := by
  ext ω
  simp [normalizedRhoGammaOpNormEvent, normalizedGammaDensityOpNormEvent]

/-! ## Deterministic radial bridge -/

omit [DecidableEq p] [DecidableEq q] in
/-- Exact radial identity for the normalized density matrix. -/
theorem rho_eq_mass_inv_smul_rawWishart (G : SampleMatrix p q σ) :
    rho G =
      ((frobeniusMass G : ℂ)⁻¹) •
        rawWishart (p := p) (q := q) (σ := σ) G := by
  ext i j
  simp [rho, normalizedSample, densityMatrix, rawWishart, frobeniusMass,
    frobeniusNorm, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  ring_nf

omit [DecidableEq p] [DecidableEq q] in
/-- Exact radial identity for the normalized partially transposed density
matrix. -/
theorem rhoGamma_eq_mass_inv_smul_rawWishartGamma (G : SampleMatrix p q σ) :
    rhoGamma G =
      ((frobeniusMass G : ℂ)⁻¹) •
        rawWishartGamma (p := p) (q := q) (σ := σ) G := by
  rw [rhoGamma, rho_eq_mass_inv_smul_rawWishart]
  ext i j
  simp [rawWishartGamma, gamma]

omit [DecidableEq p] [DecidableEq q] in
/-- Exact radial scaling of the raw partially transposed Wishart matrix.

This is the deterministic identity behind the Gaussian-to-spherical ratio:
if `Y = G / ‖G‖₂` and `T = ‖G‖₂²`, then
`(G Gᴴ)^Γ = T • ((Y Yᴴ)^Γ)`.  The statement is totalized at `G = 0`,
matching the repository's total `normalizedSample`. -/
theorem rawWishartGamma_eq_mass_smul_rhoGamma (G : SampleMatrix p q σ) :
    rawWishartGamma (p := p) (q := q) (σ := σ) G =
      ((frobeniusMass G : ℂ)) • rhoGamma (p := p) (q := q) (σ := σ) G := by
  by_cases hG : G = 0
  · ext i j
    simp [hG, rawWishartGamma, rawWishart, rhoGamma, rho, normalizedSample,
      densityMatrix]
  · rw [rhoGamma_eq_mass_inv_smul_rawWishartGamma (G := G)]
    rw [smul_smul]
    have hmass_ne : (frobeniusMass G : ℂ) ≠ 0 := by
      have hmass_pos : 0 < frobeniusMass G := by
        unfold frobeniusMass frobeniusNorm
        positivity
      exact_mod_cast ne_of_gt hmass_pos
    simp [hmass_ne]

/-- Trace-power form of the raw PT radial scaling.

This is the pointwise algebraic identity used before taking expectations in
`deletedColumnSphericalMoment_eq_ptGaussianWickRatio`: the Gaussian PT trace
moment factors as the `k`-th power of the radial mass times the spherical PT
trace moment. -/
theorem trace_pow_rawWishartGamma_eq_mass_pow_mul_trace_pow_rhoGamma
    (G : SampleMatrix p q σ) (k : ℕ) :
    ((rawWishartGamma (p := p) (q := q) (σ := σ) G) ^ k).trace =
      ((frobeniusMass G : ℂ) ^ k) *
        (((rhoGamma (p := p) (q := q) (σ := σ) G) ^ k).trace) := by
  rw [rawWishartGamma_eq_mass_smul_rhoGamma (G := G)]
  simp [Matrix.trace_smul, smul_pow]
  change ((frobeniusMass G ^ k : ℝ) : ℂ) *
        ((rhoGamma (p := p) (q := q) (σ := σ) G) ^ k).trace =
      (↑(frobeniusMass G) : ℂ) ^ k *
        ((rhoGamma (p := p) (q := q) (σ := σ) G) ^ k).trace
  rw [Complex.ofReal_pow]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- If the sample set is nonempty, the raw Wishart matrix is `s` times the
normalized Wishart matrix. -/
theorem rawWishart_eq_card_smul_wishart
    (G : SampleMatrix p q σ) (hs : Fintype.card σ ≠ 0) :
    rawWishart (p := p) (q := q) (σ := σ) G =
      (Fintype.card σ : ℂ) • wishart G := by
  rw [wishart_eq_card_inv_smul_rawWishart]
  rw [smul_smul]
  simp [hs]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- If the sample set is nonempty, the raw partially transposed Wishart matrix
is `s` times the normalized partially transposed Wishart matrix. -/
theorem rawWishartGamma_eq_card_smul_wishartGamma
    (G : SampleMatrix p q σ) (hs : Fintype.card σ ≠ 0) :
    rawWishartGamma (p := p) (q := q) (σ := σ) G =
      (Fintype.card σ : ℂ) • wishartGamma G := by
  rw [wishartGamma_eq_card_inv_smul_rawWishartGamma]
  rw [smul_smul]
  simp [hs]

omit [DecidableEq p] [DecidableEq q] in
/-- Exact identity `rho(G) = (s/T) • W`, where `W = (1/s) GG*`. -/
theorem rho_eq_sampleDimension_mul_mass_inv_smul_wishart
    (G : SampleMatrix p q σ) (hs : Fintype.card σ ≠ 0) :
    rho G =
      (((Fintype.card σ : ℂ) * (frobeniusMass G : ℂ)⁻¹)) • wishart G := by
  rw [rho_eq_mass_inv_smul_rawWishart, rawWishart_eq_card_smul_wishart (G := G) hs]
  rw [smul_smul]
  ring_nf

omit [DecidableEq p] [DecidableEq q] in
/-- Exact identity `rhoGamma(G) = (s/T) • W^Γ`. -/
theorem rhoGamma_eq_sampleDimension_mul_mass_inv_smul_wishartGamma
    (G : SampleMatrix p q σ) (hs : Fintype.card σ ≠ 0) :
    rhoGamma G =
      (((Fintype.card σ : ℂ) * (frobeniusMass G : ℂ)⁻¹)) • wishartGamma G := by
  rw [rhoGamma_eq_mass_inv_smul_rawWishartGamma,
    rawWishartGamma_eq_card_smul_wishartGamma (G := G) hs]
  rw [smul_smul]
  ring_nf

/-- Operator-norm form of `rho(G) = (s/T)W`. -/
theorem rho_opNorm_eq_sampleDimension_div_mass_mul_wishart
    (G : SampleMatrix p q σ) (hs : Fintype.card σ ≠ 0)
    (hmasspos : 0 < frobeniusMass G) :
    opNorm (rho G) =
      (sampleDimension σ / frobeniusMass G) * opNorm (wishart G) := by
  have hρ :=
    rho_eq_sampleDimension_mul_mass_inv_smul_wishart
      (p := p) (q := q) (σ := σ) G hs
  rw [opNorm, hρ, map_smul, norm_smul, ← opNorm]
  have hscalar :
      ‖(↑(Fintype.card σ) * (↑(frobeniusMass G))⁻¹ : ℂ)‖ =
        sampleDimension σ / frobeniusMass G := by
    rw [norm_mul, Complex.norm_natCast, norm_inv]
    exact by
      have hnonneg : 0 ≤ frobeniusMass G := le_of_lt hmasspos
      simp [sampleDimension, abs_of_nonneg hnonneg, div_eq_mul_inv]
  rw [hscalar]

/-- Operator-norm form of `rhoGamma(G) = (s/T)W^Γ`. -/
theorem rhoGamma_opNorm_eq_sampleDimension_div_mass_mul_wishartGamma
    (G : SampleMatrix p q σ) (hs : Fintype.card σ ≠ 0)
    (hmasspos : 0 < frobeniusMass G) :
    opNorm (rhoGamma G) =
      (sampleDimension σ / frobeniusMass G) * opNorm (wishartGamma G) := by
  have hρ :=
    rhoGamma_eq_sampleDimension_mul_mass_inv_smul_wishartGamma
      (p := p) (q := q) (σ := σ) G hs
  rw [opNorm, hρ, map_smul, norm_smul, ← opNorm]
  have hscalar :
      ‖(↑(Fintype.card σ) * (↑(frobeniusMass G))⁻¹ : ℂ)‖ =
        sampleDimension σ / frobeniusMass G := by
    rw [norm_mul, Complex.norm_natCast, norm_inv]
    exact by
      have hnonneg : 0 ≤ frobeniusMass G := le_of_lt hmasspos
      simp [sampleDimension, abs_of_nonneg hnonneg, div_eq_mul_inv]
  rw [hscalar]

/-- Scalar arithmetic behind the radial bridge. -/
lemma radial_rescale_bound
    {c K D s T W : ℝ}
    (hc : 0 < c) (hD : 0 < D) (hs : 0 < s)
    (hT : c * D * s ≤ T) (hW : W ≤ K * s) (hWnonneg : 0 ≤ W) :
    (s / T) * W ≤ (K * s / c) / D := by
  have hden : 0 < c * D * s := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le hden hT
  have hfactor₁ : s / T ≤ s / (c * D * s) :=
    div_le_div_of_nonneg_left hs.le hden hT
  have hfactor₂ : s / (c * D * s) = 1 / (c * D) := by
    field_simp [hs.ne', hc.ne', hD.ne']
  have hfactor : s / T ≤ 1 / (c * D) := by
    simpa [hfactor₂] using hfactor₁
  have hfac_nonneg : 0 ≤ 1 / (c * D) := by positivity
  calc
    (s / T) * W ≤ (1 / (c * D)) * (K * s) :=
      mul_le_mul hfactor hW hWnonneg hfac_nonneg
    _ = (K * s / c) / D := by
      field_simp [hc.ne', hD.ne']

/-! ## Pointwise normalized inputs from Wishart events -/

/-- Pointwise bridge from a mass lower bound and a Wishart bound to the
normalized density operator-norm bound. -/
theorem normalized_density_opNorm_le_of_mass_and_wishart
    {c K D : ℝ} (ω : Ω p q σ)
    (hc : 0 < c) (hD : 0 < D) (hs : 0 < sampleDimension σ)
    (hMass : c * D * sampleDimension σ ≤ gaussianMass p q σ ω)
    (hWishart : wishartOpNorm p q σ ω ≤ K * sampleDimension σ) :
    opNorm (rho (gaussianMatrix p q σ ω)) ≤
      (K * sampleDimension σ / c) / D := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  have hsNat : Fintype.card σ ≠ 0 := by
    intro hzero
    have hsample : sampleDimension σ = 0 := by
      simp [sampleDimension, hzero]
    linarith
  have hmassposGaussian : 0 < gaussianMass p q σ ω := by
    exact lt_of_lt_of_le (by positivity : 0 < c * D * sampleDimension σ) hMass
  have hmasspos : 0 < frobeniusMass G := by
    simpa [G, gaussianMass] using hmassposGaussian
  have hmass : c * D * sampleDimension σ ≤ frobeniusMass G := by
    simpa [G, gaussianMass] using hMass
  have hWishart' : opNorm (wishart G) ≤ K * sampleDimension σ := by
    simpa [G, wishartOpNorm] using hWishart
  have hWnonneg : 0 ≤ opNorm (wishart G) := by
    unfold opNorm
    positivity
  rw [rho_opNorm_eq_sampleDimension_div_mass_mul_wishart
    (p := p) (q := q) (σ := σ) G hsNat hmasspos]
  exact radial_rescale_bound hc hD hs hmass hWishart' hWnonneg

/-- Pointwise bridge from a mass lower bound and a partially transposed Wishart
bound to the normalized partial-transpose density operator-norm bound. -/
theorem normalized_gamma_opNorm_le_of_mass_and_wishartGamma
    {c K D : ℝ} (ω : Ω p q σ)
    (hc : 0 < c) (hD : 0 < D) (hs : 0 < sampleDimension σ)
    (hMass : c * D * sampleDimension σ ≤ gaussianMass p q σ ω)
    (hWishartGamma : wishartGammaOpNorm p q σ ω ≤ K * sampleDimension σ) :
    opNorm (rhoGamma (gaussianMatrix p q σ ω)) ≤
      (K * sampleDimension σ / c) / D := by
  let G : SampleMatrix p q σ := gaussianMatrix p q σ ω
  have hsNat : Fintype.card σ ≠ 0 := by
    intro hzero
    have hsample : sampleDimension σ = 0 := by
      simp [sampleDimension, hzero]
    linarith
  have hmassposGaussian : 0 < gaussianMass p q σ ω := by
    exact lt_of_lt_of_le (by positivity : 0 < c * D * sampleDimension σ) hMass
  have hmasspos : 0 < frobeniusMass G := by
    simpa [G, gaussianMass] using hmassposGaussian
  have hmass : c * D * sampleDimension σ ≤ frobeniusMass G := by
    simpa [G, gaussianMass] using hMass
  have hWishartGamma' : opNorm (wishartGamma G) ≤ K * sampleDimension σ := by
    simpa [G, wishartGammaOpNorm] using hWishartGamma
  have hWnonneg : 0 ≤ opNorm (wishartGamma G) := by
    unfold opNorm
    positivity
  rw [rhoGamma_opNorm_eq_sampleDimension_div_mass_mul_wishartGamma
    (p := p) (q := q) (σ := σ) G hsNat hmasspos]
  exact radial_rescale_bound hc hD hs hmass hWishartGamma' hWnonneg

/-- Pointwise Appendix B normalized operator-norm input obtained from the
three Gaussian Wishart good events. -/
theorem normalized_operator_norm_inputs_of_wishart_events
    {c Kw Kg M : ℝ} (ω : Ω p q σ)
    (hc : 0 < c) (hD : 0 < bipartiteDimension p q)
    (hs : 0 < sampleDimension σ)
    (hKwM : Kw * sampleDimension σ / c ≤ M)
    (hKgM : Kg * sampleDimension σ / c ≤ M)
    (hMass :
      ω ∈ gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c)
    (hWishart :
      ω ∈ wishartOpNormEvent (p := p) (q := q) (σ := σ) Kw)
    (hWishartGamma :
      ω ∈ wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) Kg) :
    ω ∈ normalizedOperatorNormInputEvent
      (p := p) (q := q) (σ := σ) M (bipartiteDimension p q) := by
  have hMass' :
      c * bipartiteDimension p q * sampleDimension σ ≤ gaussianMass p q σ ω := by
    simpa [gaussianMassLowerEvent] using hMass
  have hWishart' : wishartOpNorm p q σ ω ≤ Kw * sampleDimension σ := by
    simpa [wishartOpNormEvent] using hWishart
  have hWishartGamma' :
      wishartGammaOpNorm p q σ ω ≤ Kg * sampleDimension σ := by
    simpa [wishartGammaOpNormEvent] using hWishartGamma
  constructor
  · have hρ :=
      normalized_density_opNorm_le_of_mass_and_wishart
        (p := p) (q := q) (σ := σ) (D := bipartiteDimension p q)
        ω hc hD hs hMass' hWishart'
    exact le_trans hρ (div_le_div_of_nonneg_right hKwM hD.le)
  · have hρΓ :=
      normalized_gamma_opNorm_le_of_mass_and_wishartGamma
        (p := p) (q := q) (σ := σ) (D := bipartiteDimension p q)
        ω hc hD hs hMass' hWishartGamma'
    exact le_trans hρΓ (div_le_div_of_nonneg_right hKgM hD.le)

/-! ## Probability bridge from the concrete package -/

/-- Failure of the sample operator-norm event `Ω₁` is covered by the mass
lower-tail failure or the Wishart operator-norm failure. -/
theorem normalized_sample_opNorm_event_compl_subset_bad_events
    {c K a d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hs : 0 < sampleDimension σ)
    (hKD : K * sampleDimension σ / c ≤ a ^ 2)
    (hDim : bipartiteDimension p q = d ^ 2)
    (ha : 0 ≤ a) :
    (normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d)ᶜ ⊆
      (gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c)ᶜ ∪
        (wishartOpNormEvent (p := p) (q := q) (σ := σ) K)ᶜ := by
  intro ω hω
  have hD : 0 < bipartiteDimension p q := by
    rw [hDim]
    positivity
  have hEq :
      normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d =
        normalizedDensityOpNormEvent (p := p) (q := q) (σ := σ)
          (a ^ 2) (bipartiteDimension p q) := by
    rw [hDim]
    exact normalizedSampleOpNormEvent_eq_normalizedDensityOpNormEvent
      (p := p) (q := q) (σ := σ) ha hd
  have hω' :
      ω ∈
        (normalizedDensityOpNormEvent
          (p := p) (q := q) (σ := σ) (a ^ 2) (bipartiteDimension p q))ᶜ := by
    simpa [hEq] using hω
  by_cases hMass :
      ω ∈ gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c
  · by_cases hWishart :
        ω ∈ wishartOpNormEvent (p := p) (q := q) (σ := σ) K
    · have hgood :
          ω ∈ normalizedDensityOpNormEvent
            (p := p) (q := q) (σ := σ) (a ^ 2) (bipartiteDimension p q) := by
        have hρ :=
          normalized_density_opNorm_le_of_mass_and_wishart
            (p := p) (q := q) (σ := σ) (D := bipartiteDimension p q)
            ω hc hD hs
            (by simpa [gaussianMassLowerEvent] using hMass)
            (by simpa [wishartOpNormEvent] using hWishart)
        exact le_trans hρ
          (div_le_div_of_nonneg_right hKD hD.le)
      exact False.elim (hω' hgood)
    · exact Or.inr hWishart
  · exact Or.inl hMass

/-- Failure of the partial-transpose event `Ω₂` is covered by the mass
lower-tail failure or the `W^Γ` operator-norm failure. -/
theorem normalized_rhoGamma_opNorm_event_compl_subset_bad_events
    {c K b d : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hs : 0 < sampleDimension σ)
    (hKD : K * sampleDimension σ / c ≤ b)
    (hDim : bipartiteDimension p q = d ^ 2) :
    (normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d)ᶜ ⊆
      (gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c)ᶜ ∪
        (wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) K)ᶜ := by
  intro ω hω
  have hD : 0 < bipartiteDimension p q := by
    rw [hDim]
    positivity
  have hω' :
      ω ∈
        (normalizedGammaDensityOpNormEvent
          (p := p) (q := q) (σ := σ) b (bipartiteDimension p q))ᶜ := by
    simpa [hDim, normalizedRhoGammaOpNormEvent_eq_normalizedGammaDensityOpNormEvent]
      using hω
  by_cases hMass :
      ω ∈ gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c
  · by_cases hWishartGamma :
        ω ∈ wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) K
    · have hgood :
          ω ∈ normalizedGammaDensityOpNormEvent
            (p := p) (q := q) (σ := σ) b (bipartiteDimension p q) := by
        have hρ :=
          normalized_gamma_opNorm_le_of_mass_and_wishartGamma
            (p := p) (q := q) (σ := σ) (D := bipartiteDimension p q)
            ω hc hD hs
            (by simpa [gaussianMassLowerEvent] using hMass)
            (by simpa [wishartGammaOpNormEvent] using hWishartGamma)
        exact le_trans hρ
          (div_le_div_of_nonneg_right hKD hD.le)
      exact False.elim (hω' hgood)
    · exact Or.inr hWishartGamma
  · exact Or.inl hMass

/-- The constant `M` obtained from a concrete high-probability package after
radial normalization. -/
noncomputable def normalizedOperatorNormConstantFromPackage
    (pkg : ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ)) : ℝ :=
  max (pkg.wishartConstant * sampleDimension σ / pkg.massConstant)
    (pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant)

/-- Complement inclusion: failure of the normalized Appendix B input is
covered by the mass lower failure or one of the two Wishart upper failures. -/
theorem normalized_operator_norm_inputs_compl_subset_bad_events
    {c Kw Kg M : ℝ}
    (hc : 0 < c) (hD : 0 < bipartiteDimension p q)
    (hs : 0 < sampleDimension σ)
    (hKwM : Kw * sampleDimension σ / c ≤ M)
    (hKgM : Kg * sampleDimension σ / c ≤ M) :
    (normalizedOperatorNormInputEvent
        (p := p) (q := q) (σ := σ) M (bipartiteDimension p q))ᶜ ⊆
      (gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c)ᶜ ∪
        ((wishartOpNormEvent (p := p) (q := q) (σ := σ) Kw)ᶜ ∪
          (wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) Kg)ᶜ) := by
  intro ω hω
  by_cases hMass :
      ω ∈ gaussianMassLowerEvent (p := p) (q := q) (σ := σ) c
  · by_cases hWishart :
        ω ∈ wishartOpNormEvent (p := p) (q := q) (σ := σ) Kw
    · by_cases hWishartGamma :
          ω ∈ wishartGammaOpNormEvent (p := p) (q := q) (σ := σ) Kg
      · have hgood :=
          normalized_operator_norm_inputs_of_wishart_events
            (p := p) (q := q) (σ := σ) (c := c) (Kw := Kw) (Kg := Kg)
            (M := M) ω hc hD hs hKwM hKgM hMass hWishart hWishartGamma
        exact False.elim (hω hgood)
      · exact Or.inr (Or.inr hWishartGamma)
    · exact Or.inr (Or.inl hWishart)
  · exact Or.inl hMass

/-- Exact bridge from an already-proved concrete Wishart package to the
Appendix B normalized operator-norm input, with the three tails displayed
separately. -/
theorem normalized_operator_norm_inputs_tail_from_concreteHighProbabilityBounds
    (pkg : ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ))
    (hD : 0 < bipartiteDimension p q) (hs : 0 < sampleDimension σ) :
    (gaussianMeasure p q σ).real
        ((normalizedOperatorNormInputEvent
          (p := p) (q := q) (σ := σ)
          (normalizedOperatorNormConstantFromPackage
            (p := p) (q := q) (σ := σ) pkg)
          (bipartiteDimension p q))ᶜ) ≤
      Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
        (Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) +
          Real.exp (-(pkg.tailConstant * bipartiteDimension p q))) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  let M :=
    normalizedOperatorNormConstantFromPackage
      (p := p) (q := q) (σ := σ) pkg
  have hKwM : pkg.wishartConstant * sampleDimension σ / pkg.massConstant ≤ M := by
    simp [M, normalizedOperatorNormConstantFromPackage]
  have hKgM :
      pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant ≤ M := by
    simp [M, normalizedOperatorNormConstantFromPackage]
  have hsubset :
      (normalizedOperatorNormInputEvent
          (p := p) (q := q) (σ := σ) M (bipartiteDimension p q))ᶜ ⊆
        (gaussianMassLowerEvent
            (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ ∪
          ((wishartOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.wishartConstant)ᶜ ∪
            (wishartGammaOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.gammaWishartConstant)ᶜ) :=
    normalized_operator_norm_inputs_compl_subset_bad_events
      (p := p) (q := q) (σ := σ)
      pkg.massConstant_pos hD hs hKwM hKgM
  calc
    (gaussianMeasure p q σ).real
        ((normalizedOperatorNormInputEvent
          (p := p) (q := q) (σ := σ) M (bipartiteDimension p q))ᶜ)
        ≤
        (gaussianMeasure p q σ).real
          ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ ∪
            ((wishartOpNormEvent
                (p := p) (q := q) (σ := σ) pkg.wishartConstant)ᶜ ∪
              (wishartGammaOpNormEvent
                (p := p) (q := q) (σ := σ) pkg.gammaWishartConstant)ᶜ)) := by
          exact measureReal_mono
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    _ ≤
        (gaussianMeasure p q σ).real
            ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ) +
          (gaussianMeasure p q σ).real
            ((wishartOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.wishartConstant)ᶜ ∪
              (wishartGammaOpNormEvent
                (p := p) (q := q) (σ := σ) pkg.gammaWishartConstant)ᶜ) := by
          exact measureReal_union_le _ _
    _ ≤
        (gaussianMeasure p q σ).real
            ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ) +
          ((gaussianMeasure p q σ).real
              ((wishartOpNormEvent
                (p := p) (q := q) (σ := σ) pkg.wishartConstant)ᶜ) +
            (gaussianMeasure p q σ).real
              ((wishartGammaOpNormEvent
                (p := p) (q := q) (σ := σ) pkg.gammaWishartConstant)ᶜ)) := by
          exact add_le_add le_rfl (measureReal_union_le _ _)
    _ ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
          (Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) +
            Real.exp (-(pkg.tailConstant * bipartiteDimension p q))) := by
          gcongr
          · exact pkg.massLowerTail
          · exact pkg.wishartUpperTail
          · exact pkg.wishartGammaUpperTail

/-- Tail bound for the paper event `Ω₁`, with the mass tail and Wishart tail
displayed separately. -/
theorem normalized_sample_opNorm_tail_from_concreteHighProbabilityBounds
    (pkg : ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ))
    {a d : ℝ}
    (hd : 0 < d)
    (hs : 0 < sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (ha : 0 ≤ a)
    (haDef : a ^ 2 = pkg.wishartConstant * sampleDimension σ / pkg.massConstant) :
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d)ᶜ) ≤
      Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hsubset :=
    normalized_sample_opNorm_event_compl_subset_bad_events
      (p := p) (q := q) (σ := σ) (K := pkg.wishartConstant) (a := a)
      pkg.massConstant_pos hd hs
      (by rw [← haDef])
      hDim ha
  calc
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d)ᶜ)
        ≤
        (gaussianMeasure p q σ).real
          ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ ∪
            (wishartOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.wishartConstant)ᶜ) := by
          exact measureReal_mono
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    _ ≤
        (gaussianMeasure p q σ).real
            ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ) +
          (gaussianMeasure p q σ).real
            ((wishartOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.wishartConstant)ᶜ) := by
          exact measureReal_union_le _ _
    _ ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
          Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
          gcongr
          · exact pkg.massLowerTail
          · exact pkg.wishartUpperTail

/-- Tail bound for the paper event `Ω₂`, with the mass tail and
`W^Γ` tail displayed separately. -/
theorem normalized_rhoGamma_opNorm_tail_from_concreteHighProbabilityBounds
    (pkg : ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ))
    {b d : ℝ}
    (hd : 0 < d)
    (hs : 0 < sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hbDef : b = pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant) :
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d)ᶜ) ≤
      Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
  classical
  haveI : IsProbabilityMeasure (gaussianMeasure p q σ) := by
    rw [gaussianMeasure_eq]
    infer_instance
  have hsubset :=
    normalized_rhoGamma_opNorm_event_compl_subset_bad_events
      (p := p) (q := q) (σ := σ) (K := pkg.gammaWishartConstant) (b := b)
      pkg.massConstant_pos hd hs
      (by simp [hbDef] :
        pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant ≤
          b)
      hDim
  calc
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d)ᶜ)
        ≤
        (gaussianMeasure p q σ).real
          ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ ∪
            (wishartGammaOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.gammaWishartConstant)ᶜ) := by
          exact measureReal_mono
            (h₂ := (measure_lt_top (gaussianMeasure p q σ) _).ne) hsubset
    _ ≤
        (gaussianMeasure p q σ).real
            ((gaussianMassLowerEvent
              (p := p) (q := q) (σ := σ) pkg.massConstant)ᶜ) +
          (gaussianMeasure p q σ).real
            ((wishartGammaOpNormEvent
              (p := p) (q := q) (σ := σ) pkg.gammaWishartConstant)ᶜ) := by
          exact measureReal_union_le _ _
    _ ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
          Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
          gcongr
          · exact pkg.massLowerTail
          · exact pkg.wishartGammaUpperTail

/-- Absorb a prefactor `2` into a weaker exponential, provided the exponent is
large enough. -/
lemma two_mul_exp_neg_le_exp_neg_half
    {x : ℝ} (hx : 2 * Real.log 2 ≤ x) :
    2 * Real.exp (-x) ≤ Real.exp (-(x / 2)) := by
  have hlog : Real.log 2 ≤ x / 2 := by linarith
  have hpow : 2 ≤ Real.exp (x / 2) := by
    calc
      2 = Real.exp (Real.log 2) := by rw [Real.exp_log (by norm_num : 0 < (2 : ℝ))]
      _ ≤ Real.exp (x / 2) := by exact Real.exp_le_exp.mpr hlog
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hpow hpos.le
  have hexp_split : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  calc
    2 * Real.exp (-x) ≤ Real.exp (x / 2) * Real.exp (-x) := hmul
    _ = Real.exp (-(x / 2)) := hexp_split

/-- Collapse a split tail
`exp(-c D s) + exp(-c D)` into the paper-shaped bound `exp(-d^2 / 12)`.

This packages the two purely numeric steps used repeatedly in the Appendix B
bridge:

* drop the extra sample-dimension factor `s ≥ 1`,
* absorb the remaining prefactor `2` into a weaker exponential. -/
lemma split_tail_le_paper_decay
    (pkg : ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ))
    {d tail : ℝ}
    (htail :
      tail ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
          Real.exp (-(pkg.tailConstant * bipartiteDimension p q)))
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (htailConst : pkg.tailConstant = (1 / 6 : ℝ))
    (hLarge : 12 * Real.log 2 ≤ d ^ 2) :
    tail ≤ Real.exp (-((1 / 12 : ℝ) * d ^ 2)) := by
  have hDnonneg : 0 ≤ bipartiteDimension p q := by
    rw [hDim]
    positivity
  have hdrop :
      Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
    apply Real.exp_le_exp.mpr
    have hbase_nonneg :
        0 ≤ pkg.tailConstant * bipartiteDimension p q := by
      exact mul_nonneg pkg.tailConstant_pos.le hDnonneg
    have hmul :
        pkg.tailConstant * bipartiteDimension p q ≤
          pkg.tailConstant * bipartiteDimension p q * sampleDimension σ := by
      calc
        pkg.tailConstant * bipartiteDimension p q =
            pkg.tailConstant * bipartiteDimension p q * 1 := by ring
        _ ≤ pkg.tailConstant * bipartiteDimension p q * sampleDimension σ := by
            exact mul_le_mul_of_nonneg_left hs hbase_nonneg
    exact neg_le_neg hmul
  have hx : 2 * Real.log 2 ≤ pkg.tailConstant * bipartiteDimension p q := by
    rw [htailConst, hDim]
    nlinarith
  calc
    tail ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
          Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := htail
    _ ≤ 2 * Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
      linarith [hdrop]
    _ ≤ Real.exp (-((pkg.tailConstant / 2) * bipartiteDimension p q)) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (two_mul_exp_neg_le_exp_neg_half
          (x := pkg.tailConstant * bipartiteDimension p q) hx)
    _ = Real.exp (-((1 / 12 : ℝ) * d ^ 2)) := by
      rw [htailConst, hDim]
      congr 1
      ring

/-- Same bridge in the paper's `C exp(-cD)` form, with explicit prefactor
`C = 3`, when the sample set is nonempty. -/
theorem normalized_operator_norm_inputs_tail_expD_from_concreteHighProbabilityBounds
    (pkg : ConcreteHighProbabilityBounds (p := p) (q := q) (σ := σ))
    (hD : 0 < bipartiteDimension p q) (hs : 1 ≤ sampleDimension σ) :
    (gaussianMeasure p q σ).real
        ((normalizedOperatorNormInputEvent
          (p := p) (q := q) (σ := σ)
          (normalizedOperatorNormConstantFromPackage
            (p := p) (q := q) (σ := σ) pkg)
          (bipartiteDimension p q))ᶜ) ≤
      3 * Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
  have hspos : 0 < sampleDimension σ := lt_of_lt_of_le zero_lt_one hs
  have htail :=
    normalized_operator_norm_inputs_tail_from_concreteHighProbabilityBounds
      (p := p) (q := q) (σ := σ) pkg hD hspos
  have hdrop :
      Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
    apply Real.exp_le_exp.mpr
    have hbase_nonneg :
        0 ≤ pkg.tailConstant * bipartiteDimension p q := by
      exact mul_nonneg pkg.tailConstant_pos.le hD.le
    have hmul :
        pkg.tailConstant * bipartiteDimension p q ≤
          pkg.tailConstant * bipartiteDimension p q * sampleDimension σ := by
      calc
        pkg.tailConstant * bipartiteDimension p q =
            pkg.tailConstant * bipartiteDimension p q * 1 := by ring
        _ ≤ pkg.tailConstant * bipartiteDimension p q * sampleDimension σ := by
            exact mul_le_mul_of_nonneg_left hs hbase_nonneg
    exact neg_le_neg hmul
  calc
    (gaussianMeasure p q σ).real
        ((normalizedOperatorNormInputEvent
          (p := p) (q := q) (σ := σ)
          (normalizedOperatorNormConstantFromPackage
            (p := p) (q := q) (σ := σ) pkg)
          (bipartiteDimension p q))ᶜ)
        ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q * sampleDimension σ)) +
          (Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) +
            Real.exp (-(pkg.tailConstant * bipartiteDimension p q))) := htail
    _ ≤
        Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) +
          (Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) +
            Real.exp (-(pkg.tailConstant * bipartiteDimension p q))) := by
          exact add_le_add hdrop le_rfl
    _ = 3 * Real.exp (-(pkg.tailConstant * bipartiteDimension p q)) := by
          ring

/-- Paper-shaped separate tails for the two normalized good sets `Ω₁` and
`Ω₂`, with the prefactor absorbed into a weaker exponent for sufficiently
large `d`. -/
theorem ConcreteNormalizedOperatorNormInputsPaperForm
    {d : ℝ}
    (hd : 0 < d)
    (hs : 1 ≤ sampleDimension σ)
    (hDim : bipartiteDimension p q = d ^ 2)
    (hLarge : 12 * Real.log 2 ≤ d ^ 2) :
    let pkg := concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)
    let a := Real.sqrt (pkg.wishartConstant * sampleDimension σ / pkg.massConstant)
    let b := pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant
    (gaussianMeasure p q σ).real
        ((normalizedSampleOpNormEvent (p := p) (q := q) (σ := σ) a d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) ∧
    (gaussianMeasure p q σ).real
        ((normalizedRhoGammaOpNormEvent (p := p) (q := q) (σ := σ) b d)ᶜ) ≤
      Real.exp (-((1 / 12 : ℝ) * d ^ 2)) := by
  let pkg := concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)
  let a := Real.sqrt (pkg.wishartConstant * sampleDimension σ / pkg.massConstant)
  let b := pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant
  have htailConst : pkg.tailConstant = (1 / 6 : ℝ) := by
    simp [pkg, concreteHighProbabilityBounds]
  have hspos : 0 < sampleDimension σ := lt_of_lt_of_le zero_lt_one hs
  have ha : 0 ≤ a := by
    simp [a]
  have haDef : a ^ 2 = pkg.wishartConstant * sampleDimension σ / pkg.massConstant := by
    have hnonneg :
        0 ≤ pkg.wishartConstant * sampleDimension σ / pkg.massConstant := by
      have hnum :
          0 ≤ pkg.wishartConstant * sampleDimension σ := by
        exact mul_nonneg pkg.wishartConstant_pos.le hspos.le
      exact div_nonneg hnum pkg.massConstant_pos.le
    simpa [a] using Real.sq_sqrt hnonneg
  have hbDef : b = pkg.gammaWishartConstant * sampleDimension σ / pkg.massConstant := by
    rfl
  have hsampleTail :=
    normalized_sample_opNorm_tail_from_concreteHighProbabilityBounds
      (p := p) (q := q) (σ := σ) pkg
      (d := d) hd hspos hDim ha haDef
  have hgammaTail :=
    normalized_rhoGamma_opNorm_tail_from_concreteHighProbabilityBounds
      (p := p) (q := q) (σ := σ) pkg
      (d := d) hd hspos hDim hbDef
  constructor
  · exact split_tail_le_paper_decay
      (p := p) (q := q) (σ := σ) pkg hsampleTail hs hDim htailConst hLarge
  · exact split_tail_le_paper_decay
      (p := p) (q := q) (σ := σ) pkg hgammaTail hs hDim htailConst hLarge

/-- Canonical no-input bridge using the already-proved concrete Gaussian
Wishart package. -/
theorem ConcreteNormalizedOperatorNormInputs :
    0 < bipartiteDimension p q →
    1 ≤ sampleDimension σ →
    (gaussianMeasure p q σ).real
        ((normalizedOperatorNormInputEvent
          (p := p) (q := q) (σ := σ)
          (normalizedOperatorNormConstantFromPackage
            (p := p) (q := q) (σ := σ)
            (concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)))
          (bipartiteDimension p q))ᶜ) ≤
      3 * Real.exp (-((1 / 6 : ℝ) * bipartiteDimension p q)) := by
  intro hD hs
  simpa [concreteHighProbabilityBounds] using
    normalized_operator_norm_inputs_tail_expD_from_concreteHighProbabilityBounds
      (p := p) (q := q) (σ := σ)
      (concreteHighProbabilityBounds (p := p) (q := q) (σ := σ)) hD hs

end HighProbabilityBounds
end PptFactorization
