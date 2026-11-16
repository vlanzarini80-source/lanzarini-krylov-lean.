
import Mathlib

namespace Lanzarini

/-!
P84.4g algebraic closure only.
This is NOT the physical fourth-derivative theorem.
The inputs below are the symbolic fourth-order coefficients of
K and M2. They must be proved independently from the physical
state jets before this lemma can be used for the final theorem.
No P79, sorry, admit, or additional axioms.
-/

/-- Coefficients of the physical moments, written as algebraic expressions.
    Their identification with actual Taylor coefficients remains an open goal. -/
private def k4 (p q d : ℝ) : ℝ :=
  -(p ^ 2 * (d ^ 2 + 4 * p ^ 2 - 2 * q ^ 2)) / 12

private def m4 (p q d : ℝ) : ℝ :=
  -(p ^ 2 * (d ^ 2 + 4 * p ^ 2 - 8 * q ^ 2)) / 12

/-- Algebraic cancellation needed after the physical jet bridges are proved. -/
theorem p84_4g_algebraic_closure (p q d : ℝ) :
    4 * p ^ 2 * (m4 p q d - p ^ 4) -
      16 * p ^ 2 * k4 p q d = p ^ 4 * d ^ 2 := by
  unfold k4 m4
  ring

#print axioms p84_4g_algebraic_closure

end Lanzarini
