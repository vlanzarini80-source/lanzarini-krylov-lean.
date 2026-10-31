import P82_2_PhysicalJets
import P81_2b3_CenteredMinorDerivative

namespace Lanzarini

/-!
P82.3: Physical observables for the R0 model.

The state is the actual four-site Jacobi evolution.
The velocity is its proven physical derivative.

This file establishes a derivative of the second
Krylov moment and of the physical variance.

No target R0 coefficient is assumed.
No sorry, admit, or new axioms.

Candidate requiring Lean CI verification.
-/

/-- Physical second moment of the Krylov index. -/
noncomputable def p82_3_M2
    (p q s delta t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      Complex.normSq
        ((p81_2_state p q s delta t) j)

/-- Physical variance, without Taylor assumptions. -/
noncomputable def p82_3_V
    (p q s delta t : ℝ) : ℝ :=
  p82_3_M2 p q s delta t -
    (p81_2b3_K p q s delta t) ^ 2

/--
The physical second moment vanishes initially.
-/
theorem p82_3_M2_zero
    (p q s delta : ℝ) :
    p82_3_M2 p q s delta 0 = 0 := by
  simp [p82_3_M2, p81_2b_state_zero,
    p81_e0, Fin.sum_univ_succ]

/--
The physical variance vanishes initially.
-/
theorem p82_3_V_zero
    (p q s delta : ℝ) :
    p82_3_V p q s delta 0 = 0 := by
  simp [p82_3_V, p82_3_M2_zero,
    p81_2b3_K, p81_2b_state_zero,
    p81_2b_initial_krylov_zero]

/--
Derivative of the physical second moment.

The derivative is obtained from the actual
Jacobi state and its physical velocity.
-/
theorem p82_3_M2_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p82_3_M2 p q s delta)
      (2 * ∑ j : Fin 4,
        (j.val : ℝ) ^ 2 *
          (star ((p81_2_state p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re)
      t := by

  have hstate :=
    p81_2_state_hasDerivAt p q s delta t

  have hcomponent (j : Fin 4) :
      HasDerivAt
        (fun x : ℝ =>
          (p81_2_state p q s delta x) j)
        (p81_2_velocity p q s delta t j)
        t := by
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp_hasDerivAt
      t hstate

  have hnorm (j : Fin 4) :
      HasDerivAt
        (fun x : ℝ =>
          Complex.normSq
            ((p81_2_state p q s delta x) j))
        (2 *
          (star ((p81_2_state p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re)
        t := by
    convert (Complex.hasFDerivAt_normSq
      ((p81_2_state p q s delta t) j)).comp_hasDerivAt
        t (hcomponent j) using 1 <;> ring

  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          ∑ j : Fin 4,
            (j.val : ℝ) ^ 2 *
              Complex.normSq
                ((p81_2_state p q s delta x) j))
        (∑ j : Fin 4,
          (j.val : ℝ) ^ 2 *
            (2 *
              (star ((p81_2_state p q s delta t) j) *
                (p81_2_velocity p q s delta t j)).re))
        t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hnorm j).const_mul _

  convert hsum using 1
  · rfl
  · ring

/--
Derivative of the physical variance.
No deficit coefficient is used.
-/
theorem p82_3_V_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p82_3_V p q s delta)
      (2 * ∑ j : Fin 4,
        (j.val : ℝ) ^ 2 *
          (star ((p81_2_state p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re
       -
       2 * p81_2b3_K p q s delta t *
         (2 * ∑ j : Fin 4,
           (j.val : ℝ) *
             (star ((p81_2_state p q s delta t) j) *
               (p81_2_velocity p q s delta t j)).re))
      t := by

  have hm := p82_3_M2_hasDerivAt p q s delta t
  have hk := p81_2b3_K_hasDerivAt p q s delta t

  have hsq :=
    hk.pow 2

  have hsub := hm.sub hsq

  convert hsub using 1 <;> ring

#print axioms p82_3_M2_zero
#print axioms p82_3_V_zero
#print axioms p82_3_M2_hasDerivAt
#print axioms p82_3_V_hasDerivAt

end Lanzarini
