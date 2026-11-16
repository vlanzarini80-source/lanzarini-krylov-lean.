
import Mathlib

namespace Lanzarini

/-!
P84.4g: isolated algebraic closure.

This proves only an algebraic identity.
Physical identification of the coefficients
remains an independent open obligation.

No P79.
No sorry, admit, or new axioms.
-/

private noncomputable def k4 (p q d : ℝ) : ℝ :=
  -(p ^ 2 * (d ^ 2 + 4 * p ^ 2 - 2 * q ^ 2)) / 12

private noncomputable def m4 (p q d : ℝ) : ℝ :=
  -(p ^ 2 * (d ^ 2 + 4 * p ^ 2 - 8 * q ^ 2)) / 12

theorem p84_4g_algebraic_closure (p q d : ℝ) :
    4 * p ^ 2 * (m4 p q d - p ^ 4) -
      16 * p ^ 2 * k4 p q d =
        p ^ 4 * d ^ 2 := by
  unfold k4 m4
  ring

#print axioms p84_4g_algebraic_closure

end Lanzarini
