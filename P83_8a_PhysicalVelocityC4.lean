
import P83_7g_PhysicalStateC4
import Mathlib

namespace Lanzarini

/-!
P83.8a - Physical velocity C4 regularity.

The velocity is the image of the physical
state under the constant Jacobi generator.

No P79.
No expected Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_8a_velocity_contDiff_four
    (p q s delta : ℝ) :
    ContDiff ℝ 4
      (p81_2_velocity p q s delta) := by

  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    p81_2b1_generator p q s delta

  let L :
      (Fin 4 → ℂ) →ₗ[ℝ] (Fin 4 → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ) A

  let LC :
      (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap L

  have hs :
      ContDiff ℝ 4
        (p81_2_state p q s delta) :=
    p83_7g_state_contDiff_four
      p q s delta

  have hcomp :
      ContDiff ℝ 4
        (fun t : ℝ =>
          LC (p81_2_state p q s delta t)) := by
    exact LC.contDiff.comp hs

  have heq :
      (fun t : ℝ =>
        LC (p81_2_state p q s delta t)) =
      p81_2_velocity p q s delta := by
    funext t
    change
      A.mulVec (p81_2_state p q s delta t) =
        p81_2_velocity p q s delta t
    exact
      (p81_2b1_velocity_eq_generator
        p q s delta t).symm

  rw [heq] at hcomp
  exact hcomp

#print axioms p83_8a_velocity_contDiff_four

end Lanzarini
