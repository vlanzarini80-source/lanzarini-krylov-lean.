
import P84_4q_InitialKrylovDerivative_Candidate

namespace Lanzarini

/-!
P84.4r.1: Support of the initial
physical energy channel.

Derived from the actual Jacobi Hamiltonian.
No assumed Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r1_initial_velocity_support
    (p q r d e f : ℝ) :
    (fun j : Fin 4 =>
      (j.val : ℂ) *
        p84_4l_v p q r d e f 0 j) =
      p84_4l_v p q r d e f 0 := by
  rw [p84_4m_initial_energy_channel]
  funext j
  fin_cases j <;> simp

#print axioms p84_4r1_initial_velocity_support

end Lanzarini
