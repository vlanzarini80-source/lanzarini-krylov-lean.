
import P76_6_EnergySpeedLimit

namespace Lanzarini

open scoped Matrix.Norms.Operator

/--
P77.1a: Hamiltonian-propagator commutation.

Experimental proof using Commute.exp_right.
No sorry, admit, or additional axioms.
-/
theorem p77_1a_jacobi_commutes_propagator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    jacobiComplex n a b * jacobiPropagator n a b t =
      jacobiPropagator n a b t * jacobiComplex n a b := by
  rw [jacobiPropagator_complex_time_eq]
  have hcomm :
      Commute
        (jacobiComplex n a b)
        ((t : ℂ) •
          ((-Complex.I) • jacobiComplex n a b)) := by
    simp only [smul_smul]
    exact Commute.self_smul_left _ _
  exact hcomm.exp_right.eq

#print axioms p77_1a_jacobi_commutes_propagator

end Lanzarini
