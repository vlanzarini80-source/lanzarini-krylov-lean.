
import P84_4c2_GeneralPhysicalDeficit

namespace Lanzarini

/-!
P84.4c3: General physical Krylov derivative.

General four-site real Jacobi dynamics.
All six parameters remain free.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4c3_K_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4c1_K p q r d e f)
      (p84_4c2_J p q r d e f t)
      t := by

  have h :=
    p74_krylovComplexityAt_hasDerivAt
      4
      (p84_a d e f)
      (p84_b p q r)
      t
      p81_e0

  change
    HasDerivAt
      (p84_4c1_K p q r d e f)
      (p84_4c2_J p q r d e f t)
      t at h

  exact h

#print axioms p84_4c3_K_hasDerivAt

end Lanzarini
