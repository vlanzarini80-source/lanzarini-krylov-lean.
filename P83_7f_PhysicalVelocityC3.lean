
import P83_7e_PhysicalStateC3
import Mathlib

namespace Lanzarini

/-!
P83.7f - Physical velocity C3 regularity.

Derived from the verified C3 regularity
of the physical Jacobi state and the
constant linear generator.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_7f_velocity_contDiff_three
    (p q s delta : ℝ) :
    ContDiff ℝ 3
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
      ContDiff ℝ 3
        (p81_2_state p q s delta) :=
    p83_7e_state_contDiff_three
      p q s delta

  have hcomp :
      ContDiff ℝ 3
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

#print axioms p83_7f_velocity_contDiff_three

end Lanzarini
