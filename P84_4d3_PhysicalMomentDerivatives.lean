
import P84_4d2_ComponentProbabilityDerivative

namespace Lanzarini

/-!
P84.4d3: Physical moment derivatives.

Derivatives of the first and second moments
are obtained from the physical component
probabilities.

All six Jacobi parameters remain free.

No assumed Taylor coefficients.
No expected deficit coefficients.
No P79.
No sorry, admit, or new axioms.

Candidate requiring explicit Lean CI verification.
-/

/-- Physical probability derivative expression. -/
noncomputable def p84_4d3_probability_rate
    (p q r d e f t : ℝ)
    (j : Fin 4) : ℝ :=
  2 *
    (p84_4c1_state p q r d e f t j).re *
    (p84_4c2_velocity p q r d e f t j).re +
  2 *
    (p84_4c1_state p q r d e f t j).im *
    (p84_4c2_velocity p q r d e f t j).im

/-- First moment built from component probabilities. -/
noncomputable def p84_4d3_Kprob
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) *
      p84_4d2_probability p q r d e f j t

/-- Second moment built from component probabilities. -/
noncomputable def p84_4d3_M2prob
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      p84_4d2_probability p q r d e f j t

/--
The derivative of the first probability
moment follows from the physical evolution.
-/
theorem p84_4d3_Kprob_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4d3_Kprob p q r d e f)
      (∑ j : Fin 4,
        (j.val : ℝ) *
          p84_4d3_probability_rate p q r d e f t j)
      t := by
  unfold p84_4d3_Kprob
  apply HasDerivAt.sum
  intro j hj
  convert
    (p84_4d2_probability_hasDerivAt
      p q r d e f t j).const_mul (j.val : ℝ)
    using 1
  · rfl
  · simp [p84_4d3_probability_rate]

/--
The derivative of the second probability
moment follows from the same physical jets.
-/
theorem p84_4d3_M2prob_hasDerivAt
    (p q r d e f t : ℝ) :
    HasDerivAt
      (p84_4d3_M2prob p q r d e f)
      (∑ j : Fin 4,
        (j.val : ℝ) ^ 2 *
          p84_4d3_probability_rate p q r d e f t j)
      t := by
  unfold p84_4d3_M2prob
  apply HasDerivAt.sum
  intro j hj
  convert
    (p84_4d2_probability_hasDerivAt
      p q r d e f t j).const_mul ((j.val : ℝ) ^ 2)
    using 1
  · rfl
  · simp [p84_4d3_probability_rate]

#print axioms p84_4d3_Kprob_hasDerivAt
#print axioms p84_4d3_M2prob_hasDerivAt

end Lanzarini
