
import P84_4l_PhysicalGramMinors_Candidate

namespace Lanzarini

/-!
P84.4l.1: Initial physical Gram minors.

All six Jacobi parameters remain free.
No Taylor coefficients are assumed.
No P79.
No sorry, admit, or new axioms.
-/

/-- The physical state starts at e0. -/
theorem p84_4l1_psi_zero
    (p q r d e f : ℝ) :
    p84_4l_psi p q r d e f 0 = p81_e0 := by
  unfold p84_4l_psi
  exact jacobiState_zero 4
    (p84_a d e f)
    (p84_b p q r)
    p81_e0

/-- Initial centered Krylov vector. -/
theorem p84_4l1_u_zero
    (p q r d e f : ℝ) :
    p84_4l_u p q r d e f 0 = 0 := by
  ext j
  simp [p84_4l_u,
    p84_4l1_psi_zero,
    krylovCenteredState,
    krylovComplexity,
    p81_e0,
    Fin.sum_univ_succ]

/-- All physical Gram minors vanish initially. -/
theorem p84_4l1_minor_zero
    (p q r d e f : ℝ)
    (i j : Fin 4) :
    p84_4l_minor p q r d e f 0 i j = 0 := by
  rw [p84_4l_minor_formula]
  have hu := p84_4l1_u_zero p q r d e f
  rw [hu]
  simp

#print axioms p84_4l1_psi_zero
#print axioms p84_4l1_u_zero
#print axioms p84_4l1_minor_zero

end Lanzarini
