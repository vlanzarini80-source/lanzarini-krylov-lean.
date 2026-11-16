
import P84_4f1_GeneralFourthPower

namespace Lanzarini

/-!
P84.4g physical power bridge.

Derived from the actual four-site Jacobi
Hamiltonian and previously proved powers.

No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.

This is an intermediate checkpoint,
not the complete fourth-derivative theorem.
-/

theorem p84_4g_H3_site3
    (p q r d e f : ℝ) :
    ((p84_H p q r d e f).mulVec
      ((p84_H p q r d e f).mulVec
        ((p84_H p q r d e f).mulVec
          p81_e0))) 3 =
      (p : ℂ) * (q : ℂ) * (r : ℂ) := by
  rw [p84_4b_H3]
  rfl

theorem p84_4g_H4_site3
    (p q r d e f : ℝ) :
    ((p84_H p q r d e f).mulVec
      ((p84_H p q r d e f).mulVec
        ((p84_H p q r d e f).mulVec
          ((p84_H p q r d e f).mulVec
            p81_e0)))) 3 =
      (p : ℂ) * (q : ℂ) * (r : ℂ) *
        ((d : ℂ) + (e : ℂ) + (f : ℂ)) := by
  rw [p84_4f1_H4]
  rfl

#print axioms p84_4g_H3_site3
#print axioms p84_4g_H4_site3

end Lanzarini
