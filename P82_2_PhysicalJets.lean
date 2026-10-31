
import P81_2b1_PhysicalAcceleration

namespace Lanzarini

/-!
P82.2 - Physical jets for the R0 Jacobi model.

The derivatives are obtained from the actual
four-site Jacobi evolution.

No expected deficit coefficient is assumed.
No sorry, admit, or additional axioms.

Requires GitHub Actions compilation.
-/

/-- The physical time-evolution generator. -/
noncomputable def p82_generator
    (p q s delta : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (-Complex.I) • p81_H p q s delta

/--
All genuine time derivatives of the R0 state,
at arbitrary real time.
-/
theorem p82_physical_jet
    (p q s delta : ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (p81_2_state p q s delta) t =
    ((p82_generator p q s delta) ^ k).mulVec
      (p81_2_state p q s delta t) := by
  unfold p81_2_state p82_generator
  exact p80_1_state_iteratedDeriv
    4
    (p81_a delta)
    (p81_b p q s)
    p81_e0
    k t

/--
At t = 0, every physical jet is generated
by the same Jacobi Hamiltonian.
-/
theorem p82_initial_physical_jet
    (p q s delta : ℝ)
    (k : ℕ) :
    iteratedDeriv k
      (p81_2_state p q s delta) 0 =
    ((p82_generator p q s delta) ^ k).mulVec
      p81_e0 := by
  rw [p82_physical_jet]
  rw [p81_2b_state_zero]

/--
The generator used by P82 is exactly the
generator already established in P81.
-/
theorem p82_generator_eq_p81
    (p q s delta : ℝ) :
    p82_generator p q s delta =
      p81_2b1_generator p q s delta := by
  rfl

#print axioms p82_physical_jet
#print axioms p82_initial_physical_jet
#print axioms p82_generator_eq_p81

end Lanzarini
