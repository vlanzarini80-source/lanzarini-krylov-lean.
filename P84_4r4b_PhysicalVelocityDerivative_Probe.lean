
import P84_4r2a_InitialHasDerivAt_Candidate

namespace Lanzarini

/-!
P84.4r4b: physical initial-velocity bridge.

Establishes the initial derivative of the
physical four-site Jacobi state and its
equality with the initial centered velocity.

This does not establish differentiability
of the velocity channel itself.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r4b_psi_derivative
    (p q r d e f : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun t : ℝ =>
        p84_4l_psi p q r d e f t j)
      (p84_4l_v p q r d e f 0 j)
      0 := by
  exact
    p84_4r2a_psi_hasDerivAt
      p q r d e f j

theorem p84_4r4b_velocity_bridge
    (p q r d e f : ℝ)
    (j : Fin 4) :
    deriv
      (fun t : ℝ =>
        p84_4l_psi p q r d e f t j)
      0 =
    p84_4l_v p q r d e f 0 j := by
  exact
    (p84_4r4b_psi_derivative
      p q r d e f j).deriv

#print axioms p84_4r4b_psi_derivative
#print axioms p84_4r4b_velocity_bridge

end Lanzarini
