
import P84_4r2b_CenteredFactorDerivative_Probe

namespace Lanzarini

/-!
P84.4r2c: initial physical Krylov value.

Derived from the physical initial state.
No assumed Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r2c_K_zero
    (p q r d e f : ℝ) :
    p84_4c1_K p q r d e f 0 = 0 := by
  unfold p84_4c1_K
  rw [p84_4l1_psi_zero]
  simp [krylovComplexity,
    p81_e0, Fin.sum_univ_succ]

#print axioms p84_4r2c_K_zero

end Lanzarini
