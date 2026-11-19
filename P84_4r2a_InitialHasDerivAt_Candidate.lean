
import P84_4r1_InitialVelocitySupport_Candidate

namespace Lanzarini

/-!
P84.4r2a: Physical differentiability at zero.

Both derivatives are obtained from existing
Jacobi evolution theorems.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r2a_K_hasDerivAt
    (p q r d e f : ℝ) :
    HasDerivAt
      (p84_4c1_K p q r d e f)
      0 0 := by

  have h :=
    p84_4c3_K_hasDerivAt
      p q r d e f 0

  have hz :
      p84_4c2_J p q r d e f 0 = 0 := by
    have hd :=
      p84_4d1_K_deriv_eq_J
        p q r d e f 0
    rw [← hd]
    exact p84_4q_initial_K_derivative
      p q r d e f

  rw [hz] at h
  exact h

theorem p84_4r2a_psi_hasDerivAt
    (p q r d e f : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun t : ℝ =>
        p84_4l_psi p q r d e f t j)
      (p84_4l_v p q r d e f 0 j)
      0 := by

  have h :=
    p74_jacobiState_component_hasDerivAt
      4
      (p84_a d e f)
      (p84_b p q r)
      0 p81_e0 j

  have hv :
      (((-Complex.I) •
        jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
        (jacobiState 4
          (p84_a d e f)
          (p84_b p q r)
          0 p81_e0)) j =
      p84_4l_v p q r d e f 0 j := by

    rw [jacobiState_zero]

    rw [p84_4m_initial_energy_channel]

    simp [p84_H]

  rw [hv] at h
  exact h

#print axioms p84_4r2a_K_hasDerivAt
#print axioms p84_4r2a_psi_hasDerivAt

end Lanzarini
