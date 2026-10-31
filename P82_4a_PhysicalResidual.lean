
import P82_3_PhysicalObservables

namespace Lanzarini

/-!
P82.4a: Physical R0 speed residual.

This file defines the residual from the
actual Jacobi evolution and its proven
Krylov derivative.

No assumed Taylor coefficients.
No P79 coefficient imported.
No sorry, admit, or new axioms.
-/

noncomputable def p82_4a_Kdot
    (p q s delta t : ℝ) : ℝ :=
  2 * ∑ j : Fin 4,
    (j.val : ℝ) *
      (star ((p81_2_state p q s delta t) j) *
        (p81_2_velocity p q s delta t j)).re

noncomputable def p82_4a_F
    (p q s delta t : ℝ) : ℝ :=
  4 * p ^ 2 * p82_3_V p q s delta t -
    (p82_4a_Kdot p q s delta t) ^ 2

theorem p82_4a_K_derivative
    (p q s delta t : ℝ) :
    HasDerivAt
      (p81_2b3_K p q s delta)
      (p82_4a_Kdot p q s delta t)
      t := by
  exact p81_2b3_K_hasDerivAt p q s delta t

theorem p82_4a_F_identity
    (p q s delta t : ℝ) :
    p82_4a_F p q s delta t =
      4 * p ^ 2 * p82_3_V p q s delta t -
        (p82_4a_Kdot p q s delta t) ^ 2 := by
  rfl

theorem p82_4a_F_zero
    (p q s delta : ℝ) :
    p82_4a_F p q s delta 0 = 0 := by
  have hv := p82_3_V_zero p q s delta
  have hk :
      p82_4a_Kdot p q s delta 0 = 0 := by
    simp [p82_4a_Kdot, p81_2b_state_zero,
      p81_e0, Fin.sum_univ_succ]
  simp [p82_4a_F, hv, hk]

#print axioms p82_4a_K_derivative
#print axioms p82_4a_F_identity
#print axioms p82_4a_F_zero

end Lanzarini
