
import P84_4n_FirstMinorDerivativeReduction_Candidate

namespace Lanzarini

/-!
P84.4o: Initial physical state derivative.

Derived from the actual Jacobi evolution.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4o_initial_state_derivative
    (p q r d e f : ℝ) :
    deriv
      (fun t : ℝ =>
        p84_4l_psi p q r d e f t)
      0 =
    ((-Complex.I) •
      p84_H p q r d e f).mulVec p81_e0 := by

  unfold p84_4l_psi

  change
    deriv
      (fun t : ℝ =>
        jacobiState 4
          (p84_a d e f)
          (p84_b p q r)
          t p81_e0)
      0 =
    ((-Complex.I) •
      jacobiComplex 4
        (p84_a d e f)
        (p84_b p q r)).mulVec p81_e0

  have h :=
    p80_1_initial_derivative
      4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0
      1

  simpa only [
    iteratedDeriv_one,
    pow_one
  ] using h

#print axioms p84_4o_initial_state_derivative

end Lanzarini
