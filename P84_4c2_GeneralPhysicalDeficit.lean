
import P84_4c1_GeneralPhysicalObservables

namespace Lanzarini

/-!
P84.4c2: General physical velocity and deficit.

All six Jacobi parameters remain free.

The velocity is constructed from the physical
Hamiltonian and the evolving state.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.

Candidate: requires Lean CI verification.
-/

/-- Physical Schrodinger velocity: -i H psi(t). -/
noncomputable def p84_4c2_velocity
    (p q r d e f t : ℝ) : Fin 4 → ℂ :=
  (((-Complex.I) • p84_H p q r d e f).mulVec
    (p84_4c1_state p q r d e f t))

/-- Physical expression for the Krylov velocity. -/
noncomputable def p84_4c2_J
    (p q r d e f t : ℝ) : ℝ :=
  2 * ∑ j : Fin 4,
    (j.val : ℝ) *
      (star (p84_4c1_state p q r d e f t j) *
        p84_4c2_velocity p q r d e f t j).re

/-- Unnormalized physical Krylov speed deficit. -/
noncomputable def p84_4c2_D
    (p q r d e f t : ℝ) : ℝ :=
  4 * p ^ 2 * p84_4c1_V p q r d e f t -
    (p84_4c2_J p q r d e f t) ^ 2

/-- Velocity is constructed from the Hamiltonian. -/
theorem p84_4c2_velocity_identity
    (p q r d e f t : ℝ) :
    p84_4c2_velocity p q r d e f t =
      (((-Complex.I) • p84_H p q r d e f).mulVec
        (p84_4c1_state p q r d e f t)) := by
  rfl

/-- Definitional identity for the physical deficit. -/
theorem p84_4c2_D_identity
    (p q r d e f t : ℝ) :
    p84_4c2_D p q r d e f t =
      4 * p ^ 2 * p84_4c1_V p q r d e f t -
        (p84_4c2_J p q r d e f t) ^ 2 := by
  rfl

#print axioms p84_4c2_velocity_identity
#print axioms p84_4c2_D_identity

end Lanzarini
