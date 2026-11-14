
import P84_4d2_ComponentProbabilityDerivative

namespace Lanzarini

/-!
P84.4d3: Physical moment derivatives.

The derivatives of the first and second
probability moments are derived from the
physical Jacobi evolution.

All six real parameters remain free.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/-- Derivative expression for a component probability. -/
noncomputable def p84_4d3_probability_rate
    (p q r d e f t : ℝ)
    (j : Fin 4) : ℝ :=
  2 *
    (p84_4c1_state p q r d e f t j).re *
    (p84_4c2_velocity p q r d e f t j).re +
  2 *
    (p84_4c1_state p q r d e f t j).im *
    (p84_4c2_velocity p q r d e f t j).im

/-- First moment of physical component probabilities. -/
noncomputable def p84_4d3_Kprob
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) *
      p84_4d2_probability p q r d e f j t

/-- Second moment of physical component probabilities. -/
noncomputable def p84_4d3_M2prob
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      p84_4d2_probability p q r d e f j t

/--
The first moment derivative is derived
from the component probability derivatives.
-/
theorem p84_4d3_Kprob_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4d3_Kprob p q r d e f)
      (∑ j : Fin 4,
        (j.val : ℝ) *
          p84_4d3_probability_rate p q r d e f t j)
      t := by
  have hsum :
      HasDerivAt
        (∑ j : Fin 4,
          fun s : ℝ =>
            (j.val : ℝ) *
              p84_4d2_probability p q r d e f j s)
        (∑ j : Fin 4,
          (j.val : ℝ) *
            p84_4d3_probability_rate p q r d e f t j)
        t := by
    apply HasDerivAt.sum
    intro j hj
    simpa only [p84_4d3_probability_rate] using
      (p84_4d2_probability_hasDerivAt
        p q r d e f t j).const_mul (j.val : ℝ)
  simpa only [Finset.sum_apply, p84_4d3_Kprob] using hsum

/--
The second moment derivative is derived
from the same physical component probabilities.
-/
theorem p84_4d3_M2prob_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4d3_M2prob p q r d e f)
      (∑ j : Fin 4,
        (j.val : ℝ) ^ 2 *
          p84_4d3_probability_rate p q r d e f t j)
      t := by
  have hsum :
      HasDerivAt
        (∑ j : Fin 4,
          fun s : ℝ =>
            (j.val : ℝ) ^ 2 *
              p84_4d2_probability p q r d e f j s)
        (∑ j : Fin 4,
          (j.val : ℝ) ^ 2 *
            p84_4d3_probability_rate p q r d e f t j)
        t := by
    apply HasDerivAt.sum
    intro j hj
    simpa only [p84_4d3_probability_rate] using
      (p84_4d2_probability_hasDerivAt
        p q r d e f t j).const_mul ((j.val : ℝ) ^ 2)
  simpa only [Finset.sum_apply, p84_4d3_M2prob] using hsum

#print axioms p84_4d3_Kprob_hasDerivAt
#print axioms p84_4d3_M2prob_hasDerivAt

end Lanzarini
