
import P84_4d1_PhysicalObservableBridge

namespace Lanzarini

/-!
P84.4d2: Component probability derivative.

The result is derived from the actual
Jacobi evolution and its physical velocity.

All six real Jacobi parameters remain free.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.

Candidate: requires Lean CI verification.
-/

/--
The squared real-imaginary amplitude
of each physical state component.

This is the real expression for the
component probability.
-/
noncomputable def p84_4d2_probability
    (p q r d e f : ℝ)
    (j : Fin 4)
    (t : ℝ) : ℝ :=
  (p84_4c1_state p q r d e f t j).re ^ 2 +
  (p84_4c1_state p q r d e f t j).im ^ 2

/--
Physical derivative of the component
probability, derived from the
Schrodinger velocity.

No derivative value is assumed.
-/
theorem p84_4d2_probability_hasDerivAt
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (p84_4d2_probability p q r d e f j)
      (2 *
        (p84_4c1_state p q r d e f t j).re *
        (p84_4c2_velocity p q r d e f t j).re +
       2 *
        (p84_4c1_state p q r d e f t j).im *
        (p84_4c2_velocity p q r d e f t j).im)
      t := by

  have hparts :=
    p74_jacobiState_parts_hasDerivAt
      4
      (p84_a d e f)
      (p84_b p q r)
      t
      p81_e0
      j

  have hr :
      HasDerivAt
        (fun s : ℝ =>
          (p84_4c1_state p q r d e f s j).re)
        (p84_4c2_velocity p q r d e f t j).re
        t := by
    exact hparts.1

  have hi :
      HasDerivAt
        (fun s : ℝ =>
          (p84_4c1_state p q r d e f s j).im)
        (p84_4c2_velocity p q r d e f t j).im
        t := by
    exact hparts.2

  have hsum := (hr.pow 2).add (hi.pow 2)

  convert hsum using 1 <;>
    simp [p84_4d2_probability] <;>
    ring

#print axioms p84_4d2_probability_hasDerivAt

end Lanzarini
