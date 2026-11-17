
import P84_4i_VarianceSpeedBridge_Candidate
import P76_2_EnergyVarianceIdentity
import P77_2_EnergyMeanConservation

namespace Lanzarini

/-!
P84.4j: physical energy variance.

All six Hamiltonian parameters remain free.
The energy variance is derived from the actual
Jacobi evolution.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.

Candidate awaiting dedicated Lean CI.
-/

/-- The initial state has unit norm. -/
theorem p84_4j_initial_norm :
    jacobiNormSq p81_e0 = 1 := by
  simp [jacobiNormSq, p81_e0,
    Fin.sum_univ_succ]

/-- Initial energy expectation vanishes. -/
theorem p84_4j_initial_energy_mean
    (p q r d e f : ℝ) :
    p76_energyMean 4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0 = 0 := by
  unfold p76_energyMean
  rw [show
    (jacobiComplex 4
      (p84_a d e f)
      (p84_b p q r)).mulVec p81_e0 =
        (p84_H p q r d e f).mulVec p81_e0
    from rfl]
  rw [p84_H1]
  simp [jacobiInner, p81_e0,
    Fin.sum_univ_succ]

/-- Initial energy variance is p squared. -/
theorem p84_4j_initial_energy_variance
    (p q r d e f : ℝ) :
    p76_energyVariance 4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0 = p ^ 2 := by
  rw [p76_energyVariance_identity
    4 (p84_a d e f)
    (p84_b p q r)
    p81_e0 p84_4j_initial_norm]
  rw [p84_4j_initial_energy_mean]
  change
    jacobiNormSq
      ((p84_H p q r d e f).mulVec p81_e0) -
      0 ^ 2 = p ^ 2
  rw [p84_H1]
  simp [jacobiNormSq, Fin.sum_univ_succ,
    Complex.normSq_ofReal]

/--
Energy variance is conserved under the
actual finite Jacobi evolution.
-/
theorem p84_4j_energy_variance_conserved
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    p76_energyVarianceAt n a b t psi =
      p76_energyVariance n a b psi := by

  rw [p76_energyVarianceAt_identity
    n a b t psi hnorm]

  rw [p77_1b_hamiltonian_intertwining]

  rw [jacobiNormSq_state]

  rw [p77_2_energyMean_conserved]

  rw [p76_energyVariance_identity
    n a b psi hnorm]

/-- The physical energy variance is p squared. -/
theorem p84_4j_physical_energy_variance
    (p q r d e f t : ℝ) :
    p76_energyVarianceAt 4
      (p84_a d e f)
      (p84_b p q r)
      t p81_e0 = p ^ 2 := by
  rw [p84_4j_energy_variance_conserved
    4 (p84_a d e f)
    (p84_b p q r)
    t p81_e0
    p84_4j_initial_norm]
  exact p84_4j_initial_energy_variance
    p q r d e f

#print axioms p84_4j_initial_norm
#print axioms p84_4j_initial_energy_mean
#print axioms p84_4j_initial_energy_variance
#print axioms p84_4j_energy_variance_conserved
#print axioms p84_4j_physical_energy_variance

end Lanzarini
