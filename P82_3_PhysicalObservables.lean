
import P82_2_PhysicalJets
import P81_2b3_CenteredMinorDerivative
import P82_NormSqProbe

namespace Lanzarini

/-!
P82.3: Physical second moment and variance.

Derivative of the actual Jacobi evolution.
No assumed R0 Taylor coefficients.
No sorry, admit, or new axioms.

Candidate for Lean CI verification.
-/

noncomputable def p82_3_M2
    (p q s delta t : ℝ) : ℝ :=
  ∑ j : Fin 4,
    (j.val : ℝ) ^ 2 *
      Complex.normSq
        ((p81_2_state p q s delta t) j)

noncomputable def p82_3_V
    (p q s delta t : ℝ) : ℝ :=
  p82_3_M2 p q s delta t -
    (p81_2b3_K p q s delta t) ^ 2

theorem p82_3_M2_zero
    (p q s delta : ℝ) :
    p82_3_M2 p q s delta 0 = 0 := by
  simp [p82_3_M2, p81_2b_state_zero,
    p81_e0, Fin.sum_univ_succ]

theorem p82_3_V_zero
    (p q s delta : ℝ) :
    p82_3_V p q s delta 0 = 0 := by
  simp [p82_3_V, p82_3_M2_zero,
    p81_2b3_K, p81_2b_state_zero,
    p81_2b_initial_krylov_zero]

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

    let L : (Fin 4 → ℂ) →ₗ[ℝ] ℂ :=
      {
        toFun := fun v => v j
        map_add' := by
          intro x y
          rfl
        map_smul' := by
          intro c x
          rfl
      }

    let LC : (Fin 4 → ℂ) →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap L

    have h :=
      LC.hasFDerivAt.comp_hasDerivAt t hstate

    exact h

  have hnorm (j : Fin 4) :
      HasDerivAt
        (fun x : ℝ =>
          Complex.normSq
            ((p81_2_state p q s delta x) j))
        (2 *
          (star ((p81_2_state p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re)
        t := by

    let f : ℝ → ℂ :=
      fun x => (p81_2_state p q s delta x) j

    let dz : ℂ :=
      p81_2_velocity p q s delta t j

    have hc : HasDerivAt f dz t := by
      exact hcomponent j

    have hre :
        HasDerivAt
          (fun x : ℝ => (f x).re)
          dz.re t := by
      have h :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc
      exact h

    have him :
        HasDerivAt
          (fun x : ℝ => (f x).im)
          dz.im t := by
      have h :=
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hc
      exact h

    exact p82_normSq_probe f t dz hre him

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

  change
    HasDerivAt
      (fun x : ℝ =>
        ∑ j : Fin 4,
          (j.val : ℝ) ^ 2 *
            Complex.normSq
              ((p81_2_state p q s delta x) j))
      (2 * ∑ j : Fin 4,
        (j.val : ℝ) ^ 2 *
          (star ((p81_2_state p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re)
      t

  convert hsum using 1
  rw [Finset.mul_sum]
  congr 1
  funext j
  ring

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

  have hm :=
    p82_3_M2_hasDerivAt p q s delta t

  have hk :=
    p81_2b3_K_hasDerivAt p q s delta t

  have hsq := hk.pow 2
  have hsub := hm.sub hsq

  convert hsub using 1 <;> ring

#print axioms p82_3_M2_zero
#print axioms p82_3_V_zero
#print axioms p82_3_M2_hasDerivAt
#print axioms p82_3_V_hasDerivAt

end Lanzarini
