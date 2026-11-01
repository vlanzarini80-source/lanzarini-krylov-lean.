
import P82_4a_PhysicalResidual

namespace Lanzarini

/-!
P82.4b: Conditional derivative of the physical
R0 speed residual.

This lemma uses the genuine physical
residual defined in P82.4a.

It assumes derivative data for the
physical variance and Krylov velocity.

It does not assume Taylor coefficients,
derivative cancellations, or the target
short-time deficit formula.

No new axioms.
No sorry.
No admit.
-/

/--
Derivative of the physical speed residual
from established derivative hypotheses.
-/
theorem p82_4b_F_hasDerivAt
    (p q s delta t dV dKdot : ℝ)
    (hV :
      HasDerivAt
        (p82_3_V p q s delta)
        dV t)
    (hKdot :
      HasDerivAt
        (p82_4a_Kdot p q s delta)
        dKdot t) :
    HasDerivAt
      (p82_4a_F p q s delta)
      (4 * p ^ 2 * dV -
        2 * p82_4a_Kdot p q s delta t * dKdot)
      t := by

  have h1 :=
    hV.const_mul (4 * p ^ 2)

  have h2 :=
    hKdot.pow 2

  have h3 :=
    h1.sub h2

  change
    HasDerivAt
      (fun x : ℝ =>
        4 * p ^ 2 * p82_3_V p q s delta x -
          (p82_4a_Kdot p q s delta x) ^ 2)
      (4 * p ^ 2 * dV -
        2 * p82_4a_Kdot p q s delta t * dKdot)
      t

  convert h3 using 1 <;> ring

#print axioms p82_4b_F_hasDerivAt

end Lanzarini
