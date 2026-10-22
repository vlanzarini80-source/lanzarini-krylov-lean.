
import P75_4_DerivativeSpeedBound

namespace Lanzarini

/-!
P76.1: Energy expectation and centered
energy variance for finite Jacobi dynamics.

This file introduces the energy quantities
needed for the sharpened Krylov speed limit.

No speed-limit inequality is assumed.
-/

/--
Real energy expectation of a state.
-/
noncomputable def p76_energyMean
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ) : ℝ :=
  (jacobiInner u
    ((jacobiComplex n a b).mulVec u)).re

/--
Centered energy vector:
(H - <H>)u.
-/
noncomputable def p76_centeredEnergy
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ) : Fin n → ℂ :=
  fun j =>
    ((jacobiComplex n a b).mulVec u) j -
      (p76_energyMean n a b u : ℂ) * u j

/--
Energy variance as the squared norm
of the centered energy vector.

For normalized states and Hermitian H,
this is the usual physical variance.
-/
noncomputable def p76_energyVariance
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ) : ℝ :=
  jacobiNormSq
    (p76_centeredEnergy n a b u)

/--
Energy variance is nonnegative.
-/
theorem p76_energyVariance_nonneg
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ) :
    0 ≤ p76_energyVariance n a b u := by

  unfold p76_energyVariance
  unfold jacobiNormSq

  apply Finset.sum_nonneg
  intro j hj

  exact Complex.normSq_nonneg _

/--
Energy variance along Jacobi evolution.
-/
noncomputable def p76_energyVarianceAt
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ) : ℝ :=
  p76_energyVariance n a b
    (jacobiState n a b t psi)

/--
Nonnegativity along the evolution.
-/
theorem p76_energyVarianceAt_nonneg
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ) :
    0 ≤ p76_energyVarianceAt n a b t psi := by

  unfold p76_energyVarianceAt

  exact p76_energyVariance_nonneg
    n a b (jacobiState n a b t psi)

#print axioms p76_energyVariance_nonneg
#print axioms p76_energyVarianceAt_nonneg

end Lanzarini
