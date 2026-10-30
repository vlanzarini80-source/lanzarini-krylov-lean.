
import P81_2b2_PhysicalMinorDerivative

namespace Lanzarini

/-!
P81.2b3 - Physical Krylov derivative.

Stage A: derivative of the genuine physical
Krylov complexity along Jacobi evolution.

No assumed Taylor coefficients.
No assumed Gram-minor derivative.
No assumed deficit coefficient.
No sorry, admit, or new axioms.
-/

noncomputable def p81_2b3_K
    (p q s delta t : ℝ) : ℝ :=
  krylovComplexity
    (p81_2_state p q s delta t)

theorem p81_2b3_K_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p81_2b3_K p q s delta)
      (2 * (∑ j : Fin 4,
        (j.val : ℝ) *
          (star ((p81_2_state p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re))
      t := by

  have h :=
    p74_krylovComplexityAt_hasDerivAt
      4
      (p81_a delta)
      (p81_b p q s)
      t
      p81_e0

  change
    HasDerivAt
      (p81_2b3_K p q s delta)
      (2 * (∑ j : Fin 4,
        (j.val : ℝ) *
          (star ((p81_2_state p q s delta t) j) *
            ((p81_2b1_generator p q s delta).mulVec
              (p81_2_state p q s delta t)) j).re))
      t at h

  rw [← p81_2b1_velocity_eq_generator
    p q s delta t] at h

  exact h

#print axioms p81_2b3_K_hasDerivAt

end Lanzarini
