
import P77_1b_HamiltonianIntertwining

namespace Lanzarini

/-!
P77.2: Conservation of Jacobi energy expectation.

The proof derives energy conservation from:
1. Hamiltonian-evolution intertwining (P77.1b).
2. Preservation of inner products (P54).

No normalization assumption.
No sorry or admit.
No new axioms.
-/

/--
The complex energy expectation is conserved
under finite Jacobi evolution.
-/
theorem p77_2_energy_pair_conserved
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ) :
    jacobiInner
        (jacobiState n a b t psi)
        ((jacobiComplex n a b).mulVec
          (jacobiState n a b t psi)) =
      jacobiInner
        psi
        ((jacobiComplex n a b).mulVec psi) := by
  rw [p77_1b_hamiltonian_intertwining]
  exact jacobiInner_state_pair
    n a b t psi
    ((jacobiComplex n a b).mulVec psi)

/--
The real energy mean is constant in time.

The result requires no state normalization.
-/
theorem p77_2_energyMean_conserved
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ) :
    p76_energyMean n a b
        (jacobiState n a b t psi) =
      p76_energyMean n a b psi := by
  unfold p76_energyMean
  exact congrArg Complex.re
    (p77_2_energy_pair_conserved
      n a b t psi)

#print axioms p77_2_energy_pair_conserved
#print axioms p77_2_energyMean_conserved

end Lanzarini
