
import P82_6_PhysicalResidualDerivative

namespace Lanzarini

/-!
P82.7: Initial physical residual cancellation.

The calculation uses the genuine initial state
and physical velocity of the four-site Jacobi system.

No Taylor coefficient is assumed.
No deficit coefficient is assumed.
-/

/--
The first physical derivative of the
Krylov variance vanishes at the origin.
-/
theorem p82_7_Vdot_zero
    (p q s delta : ℝ) :
    p82_6_Vdot p q s delta 0 = 0 := by
  simp [p82_6_Vdot,
    p81_2b_state_zero,
    p81_2b_velocity_at_zero,
    p81_e0,
    Fin.sum_univ_succ]

/--
The first derivative of the physical
speed residual vanishes at time zero.
-/
theorem p82_7_F_initial_hasDerivAt
    (p q s delta : ℝ) :
    HasDerivAt
      (p82_4a_F p q s delta)
      0
      0 := by

  have hF :=
    p82_6_F_hasDerivAt
      p q s delta 0

  have hV :=
    p82_7_Vdot_zero p q s delta

  have hK :
      p82_4a_Kdot p q s delta 0 = 0 := by
    simp [p82_4a_Kdot,
      p81_2b_state_zero,
      p81_2b_velocity_at_zero,
      p81_e0,
      Fin.sum_univ_succ]

  rw [hV, hK] at hF
  convert hF using 1 <;> ring

#print axioms p82_7_Vdot_zero
#print axioms p82_7_F_initial_hasDerivAt

end Lanzarini
