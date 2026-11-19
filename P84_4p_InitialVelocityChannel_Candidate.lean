
import P84_4o_InitialPhysicalStateDerivative_Candidate

namespace Lanzarini

/-!
P84.4p: Initial physical velocity channel.

Connect the genuine derivative of the
Jacobi evolution with the physical
centered-energy channel at time zero.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4p_initial_velocity_channel
    (p q r d e f : ℝ) :
    deriv
      (fun t : ℝ =>
        p84_4l_psi p q r d e f t)
      0 =
    p84_4l_v p q r d e f 0 := by

  rw [p84_4o_initial_state_derivative]
  rw [p84_4m_initial_energy_channel]

  ext j
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct,
      p84_H, p84_a, p84_b,
      jacobiComplex, jacobiReal,
      jacobiRealEntry, p81_e0,
      Fin.sum_univ_succ]

#print axioms p84_4p_initial_velocity_channel

end Lanzarini
