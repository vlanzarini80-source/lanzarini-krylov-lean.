
import P82_4b_PhysicalResidualDerivative
import P81_2b2_PhysicalMinorDerivative

namespace Lanzarini

/-!
P82.4c: Physical acceleration bridge.

The acceleration is derived from the
actual four-site Jacobi evolution.

No assumed Taylor coefficients.
No assumed deficit formula.
No new axioms.
No sorry.
No admit.
-/

/--
The physical velocity has the physical
acceleration as its derivative.
-/
theorem p82_4c_velocity_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p81_2_velocity p q s delta)
      (p81_2b2_acceleration p q s delta t)
      t := by
  exact
    p81_2b1_velocity_hasDerivAt
      p q s delta t

/--
The physical acceleration is the Jacobi
generator applied to the physical velocity.
-/
theorem p82_4c_acceleration_eq
    (p q s delta t : ℝ) :
    p81_2b2_acceleration p q s delta t =
      (p81_2b1_generator p q s delta).mulVec
        (p81_2_velocity p q s delta t) := by
  rfl

/--
Equivalent expression using the physical
Jacobi Hamiltonian.
-/
theorem p82_4c_acceleration_hamiltonian
    (p q s delta t : ℝ) :
    p81_2b2_acceleration p q s delta t =
      (fun j : Fin 4 =>
        -Complex.I *
          ((p81_H p q s delta).mulVec
            (p81_2_velocity p q s delta t)) j) := by
  exact
    p81_2b1_generator_action
      p q s delta
      (p81_2_velocity p q s delta t)

#print axioms p82_4c_velocity_hasDerivAt
#print axioms p82_4c_acceleration_eq
#print axioms p82_4c_acceleration_hamiltonian

end Lanzarini
