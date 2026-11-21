
import P84_4r2a_InitialHasDerivAt_Candidate

namespace Lanzarini

/-!
P84.4r2b: real centered-factor derivative.

The derivative follows from the physical
Krylov derivative already established in
P84.4r2a.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r2b_real_centered_factor
    (p q r d e f : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun t : ℝ =>
        (j.val : ℝ) -
          p84_4c1_K p q r d e f t)
      0 0 := by
  have hK :=
    p84_4r2a_K_hasDerivAt
      p q r d e f

  simpa using
    hK.const_sub (j.val : ℝ)

#print axioms p84_4r2b_real_centered_factor

end Lanzarini
