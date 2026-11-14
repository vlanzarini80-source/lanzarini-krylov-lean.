
import P84_4d3_PhysicalMomentDerivatives

namespace Lanzarini

/-!
P84.4d4: Physical moment identification.

All six Jacobi parameters remain free.
The component probabilities are identified
with the squared complex amplitudes.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/-- Physical probability equals complex norm square. -/
theorem p84_4d4_probability_eq_normSq
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    p84_4d2_probability p q r d e f j t =
      Complex.normSq
        (p84_4c1_state p q r d e f t j) := by
  simp only [
    p84_4d2_probability,
    Complex.normSq_apply
  ]

/-- Identification of the physical first moment. -/
theorem p84_4d4_Kprob_eq_K
    (p q r d e f t : ℝ) :
    p84_4d3_Kprob p q r d e f t =
      p84_4c1_K p q r d e f t := by
  simp only [
    p84_4d3_Kprob,
    p84_4c1_K
  ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [p84_4d4_probability_eq_normSq]

/-- Identification of the physical second moment. -/
theorem p84_4d4_M2prob_eq_M2
    (p q r d e f t : ℝ) :
    p84_4d3_M2prob p q r d e f t =
      p84_4c1_M2 p q r d e f t := by
  simp only [
    p84_4d3_M2prob,
    p84_4c1_M2
  ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [p84_4d4_probability_eq_normSq]

#print axioms p84_4d4_probability_eq_normSq
#print axioms p84_4d4_Kprob_eq_K
#print axioms p84_4d4_M2prob_eq_M2

end Lanzarini
