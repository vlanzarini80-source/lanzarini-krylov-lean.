
import P81_2b1_PhysicalAcceleration

namespace Lanzarini

/-!
P81.2b.2 - Physical Gram-coordinate derivative.

This checkpoint derives the time derivative
of the uncentered physical Gram coordinate
from the actual Jacobi state and velocity.

The centered physical minor remains a
separate proof obligation.

No assumed Taylor coefficients.
No assumed saturation-deficit coefficients.
No sorry, admit, or new axioms.
-/

/-- Physical acceleration from the Jacobi generator. -/
noncomputable def p81_2b2_acceleration
    (p q s delta t : ℝ) : Fin 4 → ℂ :=
  (p81_2b1_generator p q s delta).mulVec
    (p81_2_velocity p q s delta t)

/-- Physical state and velocity determinant. -/
noncomputable def p81_2b2_rawMinor
    (p q s delta t : ℝ)
    (i j : Fin 4) : ℂ :=
  krylovGramCoordinate
    (p81_2_state p q s delta t)
    (p81_2_velocity p q s delta t)
    i j

/--
The derivative of the raw physical minor
follows from the physical state derivative,
the physical velocity derivative, and the
previously established Gram product rule.
-/
theorem p81_2b2_rawMinor_hasDerivAt
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    HasDerivAt
      (fun x : ℝ =>
        p81_2b2_rawMinor p q s delta x i j)
      ((p81_2_velocity p q s delta t) i *
          (p81_2_velocity p q s delta t) j +
        (p81_2_state p q s delta t) i *
          (p81_2b2_acceleration p q s delta t) j -
        ((p81_2_velocity p q s delta t) j *
            (p81_2_velocity p q s delta t) i +
          (p81_2_state p q s delta t) j *
            (p81_2b2_acceleration p q s delta t) i))
      t := by

  have hs :=
    p81_2_state_hasDerivAt p q s delta t

  have hv :=
    p81_2b1_velocity_hasDerivAt
      p q s delta t

  have hsi := hs.apply i
  have hsj := hs.apply j
  have hvi := hv.apply i
  have hvj := hv.apply j

  have h :=
    p81_2_minor_product_rule
      (p81_2_state p q s delta)
      (p81_2_velocity p q s delta)
      (p81_2_velocity p q s delta t)
      (p81_2b2_acceleration p q s delta t)
      t i j hsi hsj hvi hvj

  exact h

#print axioms p81_2b2_rawMinor_hasDerivAt

end Lanzarini
