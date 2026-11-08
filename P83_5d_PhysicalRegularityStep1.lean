
import P81_2b1_PhysicalAcceleration

namespace Lanzarini

/-!
P83.5d - Physical regularity, step 1.

Global differentiability of the genuine
Jacobi state and physical velocity.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.

This does not yet establish C^4 regularity.
-/

theorem p83_5d_state_differentiable
    (p q s delta : ℝ) :
    Differentiable ℝ
      (p81_2_state p q s delta) := by
  intro t
  exact
    (p81_2_state_hasDerivAt
      p q s delta t).differentiableAt

theorem p83_5d_velocity_differentiable
    (p q s delta : ℝ) :
    Differentiable ℝ
      (p81_2_velocity p q s delta) := by
  intro t
  exact
    (p81_2b1_velocity_hasDerivAt
      p q s delta t).differentiableAt

#print axioms p83_5d_state_differentiable
#print axioms p83_5d_velocity_differentiable

end Lanzarini
