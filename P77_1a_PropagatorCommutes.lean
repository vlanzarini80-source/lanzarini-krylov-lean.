
import P76_6_EnergySpeedLimit

namespace Lanzarini

open scoped Matrix.Norms.Operator

/--
P77.1a: Hamiltonian-propagator commutation.

Candidate proof using the exponential
of a commuting scalar multiple.

No sorry, admit, or new axioms.
-/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
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
    change
      jacobiComplex n a b *
          ((t : ℂ) •
            ((-Complex.I) • jacobiComplex n a b)) =
        ((t : ℂ) •
          ((-Complex.I) • jacobiComplex n a b)) *
          jacobiComplex n a b
    simp only [smul_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  exact hcomm.exp_right.eq

#print axioms p77_1a_jacobi_commutes_propagator

end Lanzarini
