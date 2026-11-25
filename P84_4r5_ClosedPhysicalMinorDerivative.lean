import P84_4r3_PhysicalMinorBridge_Probe
import P84_4r4c_PhysicalCenteredVelocityDerivative_Probe

namespace Lanzarini

/-!
P84.4r5: closed physical first Gram minor derivative.
Derived from physical Jacobi evolution.
No auxiliary differentiability hypotheses.
No expected Taylor coefficients.
-/

theorem p84_4r5_velocity_hasDerivAt
    (p q r d e f : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun t : ℝ =>
        p84_4l_v p q r d e f t j)
      (deriv
        (fun t : ℝ =>
          p84_4l_v p q r d e f t j)
        0)
      0 := by

  have h :=
    p84_4r4c_velocity_hasDerivAt
      p q r d e f j

  simpa only [h.deriv] using h


theorem p84_4r5_first_minor_derivative
    (p q r d e f : ℝ)
    (i j : Fin 4) :
    deriv
      (fun t : ℝ =>
        p84_4l_minor p q r d e f t i j)
      0 = 0 := by

  exact
    p84_4r3_first_minor_derivative
      p q r d e f i j
      (p84_4r5_velocity_hasDerivAt
        p q r d e f j)
      (p84_4r5_velocity_hasDerivAt
        p q r d e f i)


#print axioms p84_4r5_velocity_hasDerivAt
#print axioms p84_4r5_first_minor_derivative

end Lanzarini
