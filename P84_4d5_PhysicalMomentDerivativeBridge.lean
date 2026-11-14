
import P84_4d4_PhysicalMomentIdentification

namespace Lanzarini

/-!
P84.4d5: Physical moment derivative bridge.

Transfer the derivatives of the probability
moments to the physical Jacobi observables.

All six real Jacobi parameters remain free.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/--
The physical Krylov observable has the
derivative obtained from the component
probability evolution.
-/
theorem p84_4d5_K_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4c1_K p q r d e f)
      (∑ j : Fin 4,
        (j.val : ℝ) *
          p84_4d3_probability_rate
            p q r d e f t j)
      t := by
  have heq :
      p84_4d3_Kprob p q r d e f =
        p84_4c1_K p q r d e f := by
    funext s
    exact p84_4d4_Kprob_eq_K
      p q r d e f s
  rw [← heq]
  exact p84_4d3_Kprob_hasDerivAt
    p q r d e f t

/--
The physical second moment has the
derivative obtained from the component
probability evolution.
-/
theorem p84_4d5_M2_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4c1_M2 p q r d e f)
      (∑ j : Fin 4,
        (j.val : ℝ) ^ 2 *
          p84_4d3_probability_rate
            p q r d e f t j)
      t := by
  have heq :
      p84_4d3_M2prob p q r d e f =
        p84_4c1_M2 p q r d e f := by
    funext s
    exact p84_4d4_M2prob_eq_M2
      p q r d e f s
  rw [← heq]
  exact p84_4d3_M2prob_hasDerivAt
    p q r d e f t

#print axioms p84_4d5_K_hasDerivAt
#print axioms p84_4d5_M2_hasDerivAt

end Lanzarini
