
import P83_8a_PhysicalVelocityC4
import P81_2b3_CenteredMinorDerivative
import Mathlib

namespace Lanzarini

/-!
P83.8b - Physical Krylov C4 regularity.

Explicit regularity proof for Complex.normSq.
The physical Krylov definition is unchanged.

No P79.
No expected Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_8b_K_contDiff_four
    (p q s delta : ℝ) :
    ContDiff ℝ 4
      (p81_2b3_K p q s delta) := by

  have hs :
      ContDiff ℝ 4
        (p81_2_state p q s delta) :=
    p83_7g_state_contDiff_four
      p q s delta

  have hnorm :
      ContDiff ℝ 4
        (fun z : ℂ => Complex.normSq z) := by
    unfold Complex.normSq
    fun_prop

  have hcoord (j : Fin 4) :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2_state p q s delta t) j) := by
    fun_prop

  have hterm (j : Fin 4) :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (j.val : ℝ) *
            Complex.normSq
              ((p81_2_state p q s delta t) j)) := by
    have hj :
        ContDiff ℝ 4
          (fun t : ℝ =>
            Complex.normSq
              ((p81_2_state p q s delta t) j)) :=
      hnorm.comp (hcoord j)
    exact contDiff_const.mul hj

  have hK :
      ContDiff ℝ 4
        (fun t : ℝ =>
          ∑ j : Fin 4,
            (j.val : ℝ) *
              Complex.normSq
                ((p81_2_state p q s delta t) j)) := by
    classical
    apply ContDiff.sum
    intro j hj
    exact hterm j

  simpa only [
    p81_2b3_K,
    krylovComplexity
  ] using hK

#print axioms p83_8b_K_contDiff_four

end Lanzarini
