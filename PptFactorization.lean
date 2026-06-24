-- PPT Factorization — Point d'entrée principal
-- Article: "Moment-based PPT of random bipartite quantum states"
-- Institut Fourier, Grenoble — Kieran McShane / Cécilia Lancien
import PptFactorization.Poly
import PptFactorization.Verify
import PptFactorization.Jones
-- import PptFactorization.Recurrence   -- Superseded by ClosedFormDet; 3 sorries, non-blocking
import PptFactorization.ClosedFormDet   -- Closed-form det via orthogonal polys + Chebyshev U
import PptFactorization.Threshold       -- Cor 3.1 : seuil = 4cos²(π/(m+2))
import PptFactorization.AubrunAlternative -- Moment-Hankel adapters for Aubrun threshold route
import PptFactorization.Moments         -- Moments c_k(λ) as Polynomial ℤ, recurrence
import PptFactorization.Asymmetric      -- Asymmetric p₃-PPT threshold: λ* = d₁ − 1/d₁
import PptFactorization.General         -- General p_{2m+1} thresholds, m=2, scaling law
import PptFactorization.Step6LeadingOrder -- Step 6: detB_m(α·d₁, d₁) closed forms for m=1,2
import PptFactorization.MomentCumulant   -- Moment–cumulant scaffold: c₁..c₇ from κ_n (NC deferred)
import PptFactorization.NCPartition       -- Non-crossing partitions of {0,…,n−1}: definition layer
import PptFactorization.ScalingLaw      -- Universal scaling law: λ* = αₘd₁ − 1/d₁ + O(1/d₁³)
import PptFactorization.TemperleyLieb   -- TL algebras, Gram–Hankel bridge, Markov trace
import PptFactorization.SubfactorBridge -- Jones index axiom, PPT ↔ subfactor dictionary
import PptFactorization.GJSCircle       -- GJS circle: PPT ⟺ Gram positivity ⟺ Jones index
import PptFactorization.ChristoffelDarboux -- CD identity for Chebyshev U, trace normalisation
import PptFactorization.SpectralGeometric -- Spectral-geometric proof: −1/d₁ from principal graph
import PptFactorization.Realignment       -- Realignment (CCNR) moments, Jacobi, Hankel thresholds
import PptFactorization.UniversalScalingLaw -- Universal scaling law: ε = −1 for all m (complete proof)
import PptFactorization.AppendixCMainResult -- Appendix C consolidated theorem endpoints
import PptFactorization.AppendixB          -- Appendix B: local Lipschitz concentration skeleton
import PptFactorization.AppendixBSpikeLowerBound -- Conservative spike lower-bound skeleton
import PptFactorization.AppendixBLowerBoundClosure -- Stable lower-bound closure aliases
import PptFactorization.AristotleTargets.LowerMeanLimitConcreteChoices -- Sharp lower concrete frontier and diagnostics
import PptFactorization.PartialTranspose   -- Concrete partial-transpose API and exact shuffle identity
import PptFactorization.ProbabilityTools   -- Reused Gaussian/MGF tools ported from Erdős 524
import PptFactorization.RandomMatrixModel  -- Concrete G, X, ρ_X, W, Γ, and Ω_M model objects
import PptFactorization.AubrunAlternativeModelBridge -- Model-facing λ>4 moment route adapters
import PptFactorization.GaussianModel      -- Concrete standard complex Gaussian matrix probability space
import PptFactorization.HighProbabilityBounds -- Concrete Stage 3/4 high-probability event interface
import PptFactorization.ComplexGaussianWick -- Wick/Isserlis expansion API for Gaussian entry monomials
import PptFactorization.TraceWickExpansion -- Closed-walk trace expansion plus Wick finite-sum rewrite
import PptFactorization.TraceWickProductExpansion -- Automatic closed-walk monomial expansion for Z
import PptFactorization.AubrunMomentSpine -- Surviving-contraction trace-moment spine
import PptFactorization.WickCountingCore -- Minimal polynomial counting core for Aubrun contractions
import PptFactorization.WickCountingBounds -- Polynomial counting envelopes for Wick contraction families
import PptFactorization.AppendixBConcreteModel -- Canonical `Fin d, Fin d, Fin s` Appendix B model
import PptFactorization.AppendixBWishartBridge -- Bridge from Wishart tails to normalized Appendix B inputs
import PptFactorization.AppendixBRadialSpherical -- Radial/spherical factorization interface
import PptFactorization.AppendixBSurfaceMeasure -- Canonical surface measure and true Haar polar coordinates
import PptFactorization.AppendixBLevyPolarBridge -- Bridge: canonical surface Levy + Gaussian polar law -> exact model
import PptFactorization.AppendixBNormalizedExpectations -- Normalized expectation bounds from radial/spherical factorization
import PptFactorization.AppendixBPolarRadial -- No-input Gaussian radial estimates for Appendix B
import PptFactorization.AppendixBAubrunMomentInput -- Appendix-facing Aubrun off-diagonal moment interface
import PptFactorization.AppendixBAubrunProposition71 -- Proposition 7.1-facing trace-moment closure
import PptFactorization.AppendixBFinal -- Final Appendix B assembly without structure-valued inputs
import PptFactorization.AppendixBPipeline -- Canonical moments-to-final Appendix B wiring
import PptFactorization.AppendixBDiagonalGamma -- Exact diagonal Gamma-max bridge
import PptFactorization.AppendixBGaussianIntegrability -- Closed Gaussian integrability inputs for the pipeline
import PptFactorization.AppendixBAubrunCombinatorics -- Real Wick/counting bound hooks for Aubrun
import PptFactorization.AppendixBAubrunGraduate -- Sharp trace-moment bound up to the textbook Aubrun relation count
import PptFactorization.AppendixBPipelineGraduate -- Graduate-counting bridge into the Appendix B pipeline
import PptFactorization.AppendixBTightFiberPackageEndpoint -- Package-form exact-square tight-fiber endpoint
import PptFactorization.AppendixBAubrunMotzkin -- Motzkin checkpoint for the zero-defect Aubrun frontier
import PptFactorization.AppendixBSphericalConcentration -- Surface concentration + polar law -> exact spherical model
import PptFactorization.SphericalPolarizationGeometricKernel -- Polarization kernel/Jacobian algebra
import PptFactorization.SphericalPolarizationJacobianTargets -- Canonical reflection-map target interfaces
import PptFactorization.SphericalPolarizationPushforwardTransport -- Closed surface push-forward for reflection
import PptFactorization.PolarizationLemma43Core -- Quantitative core of polarization strict improvement
import PptFactorization.MeasureTheoreticTrimming -- Generic measure trimming for polarization
import PptFactorization.PolarizationLemma43MeasureTrimming -- Measure-theoretic trimming for Lemma 4.3
import PptFactorization.SphericalPolarizationStrictImprovement -- Strict improvement from rectangular kernel blocks
import PptFactorization.UpperMixedOneQuadraticBranch -- Mixed-word deterministic one-quadratic branch
import PptFactorization.UpperMixedOneLinearBranch -- Mixed-word deterministic one-linear branch
import PptFactorization.UpperMixedMultiDefectBranch -- Mixed-word deterministic multi-defect branch
import PptFactorization.AppendixBUpperBoundClosure -- Upper-bound closure endpoints
import PptFactorization.AristotleTargets.WordProtocolLocalSpikeBridge -- A/P/C protocol to A/L/Q local-expansion bridge
