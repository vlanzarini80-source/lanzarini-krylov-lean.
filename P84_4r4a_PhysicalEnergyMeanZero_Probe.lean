
import P84_4r3_PhysicalMinorBridge_Probe
import P77_2_EnergyMeanConservation

namespace Lanzarini

/-!
P84.4r4a: physical energy mean vanishes
along the complete four-site Jacobi evolution.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r4a_energy_mean_zero
    (p q r d e f t : ℝ) :
    p76_energyMean 4
      (p84_a d e f)
      (p84_b p q r)
      (p84_4l_psi p q r d e f t) = 0 := by

  change
    p76_energyMean 4
      (p84_a d e f)
      (p84_b p q r)
      (jacobiState 4
        (p84_a d e f)
        (p84_b p q r)
        t p81_e0) = 0

  rw [p77_2_energyMean_conserved]

  exact p84_4j_initial_energy_mean
    p q r d e f

#print axioms p84_4r4a_energy_mean_zero

end Lanzarini
