
import P82_5_PhysicalKrylovAcceleration

namespace Lanzarini

/-!
P82.6: Unconditional physical derivative of
the R0 Jacobi speed residual.

The derivative is obtained from the actual
four-site Jacobi evolution.

The proof reuses:
P82.3: physical variance derivative.
P82.4b: residual product-rule theorem.
P82.5: physical Krylov second derivative.

No assumed Taylor coefficients.
No assumed cancellation orders.
No assumed deficit formula.
-/

/--
Physical derivative expression for the
Krylov variance, from the actual state
and its velocity.
-/
noncomputable def p82_6_Vdot
    (p q s delta t : ℝ) : ℝ :=
  2 * ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      (star ((p81_2_state p q s delta t) j) *
        (p81_2_velocity p q s delta t j)).re
  -
  2 * p81_2b3_K p q s delta t *
    (2 * ∑ j : Fin 4,
      (j.val : ℝ) *
        (star ((p81_2_state p q s delta t) j) *
          (p81_2_velocity p q s delta t j)).re)

/--
The physical variance has derivative
p82_6_Vdot at every real time.
-/
theorem p82_6_V_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p82_3_V p q s delta)
      (p82_6_Vdot p q s delta t)
      t := by
  exact p82_3_V_hasDerivAt p q s delta t

/--
Physical derivative of the speed residual.

This theorem has no auxiliary derivative
assumptions and uses the actual Jacobi
evolution.

It does not claim a short-time coefficient
or an order of vanishing.
-/
theorem p82_6_F_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p82_4a_F p q s delta)
      (4 * p ^ 2 * p82_6_Vdot p q s delta t -
        2 * p82_4a_Kdot p q s delta t *
          p82_5_Kddot p q s delta t)
      t := by

  have hV :
      HasDerivAt
        (p82_3_V p q s delta)
        (p82_6_Vdot p q s delta t)
        t :=
    p82_6_V_hasDerivAt p q s delta t

  have hKdot :
      HasDerivAt
        (p82_4a_Kdot p q s delta)
        (p82_5_Kddot p q s delta t)
        t :=
    p82_5_Kdot_hasDerivAt p q s delta t

  exact
    p82_4b_F_hasDerivAt
      p q s delta t
      (p82_6_Vdot p q s delta t)
      (p82_5_Kddot p q s delta t)
      hV hKdot

#print axioms p82_6_V_hasDerivAt
#print axioms p82_6_F_hasDerivAt

end Lanzarini
