
import P77_1a_PropagatorCommutes

namespace Lanzarini

open scoped Matrix.Norms.Operator

/--
P77.1b: The Jacobi Hamiltonian intertwines
with the quantum evolution of every state.

No normalization assumption is required.
No new axioms.
No sorry.
-/
theorem p77_1b_hamiltonian_intertwining
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ) :
    (jacobiComplex n a b).mulVec
        (jacobiState n a b t psi) =
      jacobiState n a b t
        ((jacobiComplex n a b).mulVec psi) := by
  unfold jacobiState
  calc
    (jacobiComplex n a b).mulVec
        ((jacobiPropagator n a b t).mulVec psi) =
      (jacobiComplex n a b *
        jacobiPropagator n a b t).mulVec psi := by
          rw [Matrix.mulVec_mulVec]
    _ =
      (jacobiPropagator n a b t *
        jacobiComplex n a b).mulVec psi := by
          rw [p77_1a_jacobi_commutes_propagator]
    _ =
      (jacobiPropagator n a b t).mulVec
        ((jacobiComplex n a b).mulVec psi) := by
          rw [Matrix.mulVec_mulVec]

#print axioms p77_1b_hamiltonian_intertwining

end Lanzarini
