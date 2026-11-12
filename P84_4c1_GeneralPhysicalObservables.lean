
import P84_4b_GeneralThirdPower

namespace Lanzarini

/-!
P84.4c1: General four-site physical observables.

The six real parameters p, q, r, d, e, f
remain free.

The observables are defined from the actual
Jacobi evolution.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.

Candidate requiring Lean CI verification.
-/

/-- Physical state of the general Jacobi matrix. -/
noncomputable def p84_4c1_state
    (p q r d e f t : ℝ) : Fin 4 → ℂ :=
  jacobiState 4
    (p84_a d e f)
    (p84_b p q r)
    t p81_e0

/-- Physical Krylov complexity. -/
noncomputable def p84_4c1_K
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) *
      Complex.normSq
        (p84_4c1_state p q r d e f t j)

/-- Physical second moment. -/
noncomputable def p84_4c1_M2
    (p q r d e f t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      Complex.normSq
        (p84_4c1_state p q r d e f t j)

/-- Physical Krylov variance. -/
noncomputable def p84_4c1_V
    (p q r d e f t : ℝ) : ℝ :=
  p84_4c1_M2 p q r d e f t -
    (p84_4c1_K p q r d e f t) ^ 2

/-- The physical initial state is e0. -/
theorem p84_4c1_state_zero
    (p q r d e f : ℝ) :
    p84_4c1_state p q r d e f 0 =
      p81_e0 := by
  unfold p84_4c1_state
  exact jacobiState_zero 4
    (p84_a d e f)
    (p84_b p q r)
    p81_e0

/-- Initial physical Krylov complexity. -/
theorem p84_4c1_K_zero
    (p q r d e f : ℝ) :
    p84_4c1_K p q r d e f 0 = 0 := by
  simp [p84_4c1_K, p84_4c1_state_zero,
    p81_e0, Fin.sum_univ_succ]

/-- Initial physical second moment. -/
theorem p84_4c1_M2_zero
    (p q r d e f : ℝ) :
    p84_4c1_M2 p q r d e f 0 = 0 := by
  simp [p84_4c1_M2, p84_4c1_state_zero,
    p81_e0, Fin.sum_univ_succ]

/-- Initial physical variance. -/
theorem p84_4c1_V_zero
    (p q r d e f : ℝ) :
    p84_4c1_V p q r d e f 0 = 0 := by
  simp [p84_4c1_V,
    p84_4c1_K_zero,
    p84_4c1_M2_zero]

#print axioms p84_4c1_state_zero
#print axioms p84_4c1_K_zero
#print axioms p84_4c1_M2_zero
#print axioms p84_4c1_V_zero

end Lanzarini
