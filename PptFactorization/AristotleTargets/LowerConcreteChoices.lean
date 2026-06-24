import PptFactorization.AppendixBLowerBoundClosure
import PptFactorization.AppendixBWishartBridge

/-!
Shared concrete choices for Aristotle lower-bound handoffs.

These are candidate definitions only.  They are not axioms and they do not
assert that the corresponding deterministic or probabilistic estimates are
proved.  Each estimate is submitted as a separate theorem target.
-/

namespace AppendixB

open Filter
open scoped Topology

noncomputable def lowerAristotleEps (ε : ℝ) (_d : ℕ) : ℝ :=
  ε

noncomputable def lowerAristotleMean (_d : ℕ) : ℝ :=
  0

noncomputable def lowerAristotleOperatorThreshold
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteN d

noncomputable def lowerAristotleTau
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta 0 0 d

noncomputable def lowerAristotleProfileError
    (_k : ℕ) (_ε : ℝ) (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

noncomputable def lowerAristotleScaleError
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_k : ℕ) (_ε : ℝ) (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

noncomputable def lowerAristotleMixedError
    (_R : _root_.PptFactorization.AppendixB.ConcreteModel.BalancedRegime)
    (_k : ℕ) (_ε : ℝ) (a slack : ℝ) (d : ℕ) : ℝ :=
  lowerConcreteDelta a slack d

noncomputable def lowerAristotleMomentBound
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-(d : ℝ))

noncomputable def lowerAristotleOperatorTailBound
    (_a _slack : ℝ) (d : ℕ) : ℝ :=
  Real.exp (-((1 / 12 : ℝ) * (d : ℝ) ^ 2))

end AppendixB
