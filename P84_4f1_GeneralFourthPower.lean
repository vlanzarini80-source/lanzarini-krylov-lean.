
import P84_4b_GeneralThirdPower

namespace Lanzarini

/-!
P84.4f1: Fourth physical Jacobi power.

Derived directly from the Hamiltonian action.
All six real parameters remain free.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No additional axioms.
-/

theorem p84_4f1_H4
    (p q r d e f : ℝ) :
    (p84_H p q r d e f).mulVec
      ((p84_H p q r d e f).mulVec
        ((p84_H p q r d e f).mulVec
          ((p84_H p q r d e f).mulVec
            p81_e0))) =
      ![
        (p : ℂ) ^ 2 *
          ((p : ℂ) ^ 2 +
           (d : ℂ) ^ 2 +
           (q : ℂ) ^ 2),

        (p : ℂ) *
          ((d : ℂ) * (p : ℂ) ^ 2 +
           (d : ℂ) *
             ((p : ℂ) ^ 2 +
              (d : ℂ) ^ 2 +
              (q : ℂ) ^ 2) +
           (q : ℂ) ^ 2 *
             ((d : ℂ) + (e : ℂ))),

        (p : ℂ) * (q : ℂ) *
          ((p : ℂ) ^ 2 +
           (d : ℂ) ^ 2 +
           (q : ℂ) ^ 2 +
           (e : ℂ) * ((d : ℂ) + (e : ℂ)) +
           (r : ℂ) ^ 2),

        (p : ℂ) * (q : ℂ) * (r : ℂ) *
          ((d : ℂ) + (e : ℂ) + (f : ℂ))
      ] := by
  rw [p84_4b_H3, p84_H_action]
  ext i
  fin_cases i <;> simp <;> ring

#print axioms p84_4f1_H4

end Lanzarini
