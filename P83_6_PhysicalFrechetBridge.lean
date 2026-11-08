
import P83_5d_PhysicalRegularityStep1
import Mathlib

namespace Lanzarini

/-!
P83.6 - Physical Frechet derivative bridge.

Converts physical time derivatives
into real Frechet derivatives.

No P79.
No expected Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_6_state_hasFDerivAt
    (p q s delta t : ℝ) :
    ∃ L : ℝ →L[ℝ] (Fin 4 → ℂ),
      HasFDerivAt
        (p81_2_state p q s delta)
        L t := by
  exact
    ⟨ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        (p81_2_velocity p q s delta t),
      (p81_2_state_hasDerivAt
        p q s delta t).hasFDerivAt⟩

theorem p83_6_velocity_hasFDerivAt
    (p q s delta t : ℝ) :
    ∃ L : ℝ →L[ℝ] (Fin 4 → ℂ),
      HasFDerivAt
        (p81_2_velocity p q s delta)
        L t := by
  exact
    ⟨ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        ((p81_2b1_generator p q s delta).mulVec
          (p81_2_velocity p q s delta t)),
      (p81_2b1_velocity_hasDerivAt
        p q s delta t).hasFDerivAt⟩

#print axioms p83_6_state_hasFDerivAt
#print axioms p83_6_velocity_hasFDerivAt

end Lanzarini
