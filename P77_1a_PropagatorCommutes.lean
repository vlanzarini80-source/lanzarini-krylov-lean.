
import P76_6_EnergySpeedLimit

namespace Lanzarini

open scoped Matrix.Norms.Operator

/--
P77.1a: Hamiltonian-propagator commutation.
Experimental proof obligation.
-/
theorem p77_1a_jacobi_commutes_propagator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    jacobiComplex n a b * jacobiPropagator n a b t =
      jacobiPropagator n a b t * jacobiComplex n a b := by
  rw [jacobiPropagator_complex_time_eq]
  exact?

#print axioms p77_1a_jacobi_commutes_propagator

end Lanzarini
