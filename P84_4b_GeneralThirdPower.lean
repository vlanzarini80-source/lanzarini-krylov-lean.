
import P84_4a_GeneralJacobiPowers

namespace Lanzarini

/-!
P84.4b: Third physical Jacobi power.

All six real parameters remain free.
The result is derived from the actual
Jacobi matrix action.

No expected deficit coefficient.
No P79.
No sorry, admit, or new axioms.
-/

/--
Third power of the general four-site
Jacobi Hamiltonian on the initial state.
-/
theorem p84_4b_H3
    (p q r d e f : ℝ) :
    (p84_H p q r d e f).mulVec
      ((p84_H p q r d e f).mulVec
        ((p84_H p q r d e f).mulVec
          p81_e0)) =
      ![
        (d : ℂ) * (p : ℂ) ^ 2,
        (p : ℂ) *
          ((p : ℂ) ^ 2 +
           (d : ℂ) ^ 2 +
           (q : ℂ) ^ 2),
        (p : ℂ) * (q : ℂ) *
          ((d : ℂ) + (e : ℂ)),
        (p : ℂ) * (q : ℂ) * (r : ℂ)
      ] := by
  rw [p84_H2, p84_H_action]
  ext i
  fin_cases i <;> simp <;> ring

#print axioms p84_4b_H3

end Lanzarini
