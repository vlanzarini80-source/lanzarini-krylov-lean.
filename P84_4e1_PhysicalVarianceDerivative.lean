
import P84_4d5_PhysicalMomentDerivativeBridge

namespace Lanzarini

/-!
P84.4e1: Derivative of physical Krylov variance.

Derived from the actual Jacobi evolution
and the previously established derivatives
of the first and second physical moments.

All six parameters remain free.
No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/-- First physical moment derivative expression. -/
noncomputable def p84_4e1_K_rate
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) *
      p84_4d3_probability_rate p q r d e f t j

/-- Second physical moment derivative expression. -/
noncomputable def p84_4e1_M2_rate
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      p84_4d3_probability_rate p q r d e f t j

/--
Physical variance derivative, obtained by
differentiating M2 - K squared.
-/
theorem p84_4e1_V_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4c1_V p q r d e f)
      (p84_4e1_M2_rate p q r d e f t -
        2 * p84_4c1_K p q r d e f t *
          p84_4e1_K_rate p q r d e f t)
      t := by

  have hK :
      HasDerivAt
        (p84_4c1_K p q r d e f)
        (p84_4e1_K_rate p q r d e f t)
        t := by
    exact p84_4d5_K_hasDerivAt
      p q r d e f t

  have hM2 :
      HasDerivAt
        (p84_4c1_M2 p q r d e f)
        (p84_4e1_M2_rate p q r d e f t)
        t := by
    exact p84_4d5_M2_hasDerivAt
      p q r d e f t

  have hV := hM2.sub (hK.pow 2)

  convert hV using 1 <;>
    simp [p84_4c1_V] <;>
    ring

#print axioms p84_4e1_V_hasDerivAt

end Lanzarini
