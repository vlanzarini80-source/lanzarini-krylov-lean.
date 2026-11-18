
import P84_4l3_PhysicalMinorDerivativeBridge_Candidate
import P84_4j_PhysicalEnergyVariance_Candidate

namespace Lanzarini

/-!
P84.4m: initial physical energy channel.

The result is derived from the physical
Jacobi Hamiltonian and its initial state.

No assumed Taylor or deficit coefficients.
No P79.
-/

/-- Initial energy channel, obtained from the
    physical Hamiltonian action. -/
theorem p84_4m_initial_energy_channel
    (p q r d e f : ℝ) :
    p84_4l_v p q r d e f 0 =
      fun j : Fin 4 =>
        -Complex.I *
          (![0, (p : ℂ), 0, 0] : Fin 4 → ℂ) j := by
  ext j
  simp only [p84_4l_v, p76_centeredEnergy]
  rw [p84_4l1_psi_zero]
  rw [p84_4j_initial_energy_mean]
  change
    -Complex.I *
      (((p84_H p q r d e f).mulVec p81_e0) j -
        (0 : ℂ) * p81_e0 j) =
      -Complex.I *
        (![0, (p : ℂ), 0, 0] : Fin 4 → ℂ) j
  rw [p84_H1]
  simp

#print axioms p84_4m_initial_energy_channel

end Lanzarini
