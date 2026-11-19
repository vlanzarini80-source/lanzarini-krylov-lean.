
import P84_4p_InitialVelocityChannel_Candidate

namespace Lanzarini

/-!
P84.4q: Initial physical Krylov derivative.

The derivative is obtained from the physical
Jacobi evolution and its observable.

No assumed Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4q_initial_K_derivative
    (p q r d e f : ℝ) :
    deriv
      (p84_4c1_K p q r d e f)
      0 = 0 := by

  rw [p84_4d1_K_deriv_eq_J]

  unfold p84_4c2_J

  rw [p84_4c1_state_zero]

  simp [p81_e0, Fin.sum_univ_succ]

#print axioms p84_4q_initial_K_derivative

end Lanzarini
