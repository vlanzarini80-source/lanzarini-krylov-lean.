
import P83_7c_PhysicalStateC2
import Mathlib

namespace Lanzarini

/-!
P83.7d - Physical velocity C2 regularity.

Derived from:
1. C2 regularity of the physical Jacobi state.
2. The exact physical identity v(t) = A * psi(t).
3. Continuity and linearity of the constant generator A.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_7d_velocity_contDiff_two
    (p q s delta : ℝ) :
    ContDiff ℝ 2
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
      ContDiff ℝ 2
        (p81_2_state p q s delta) :=
    p83_7c_state_contDiff_two
      p q s delta

  have hcomp :
      ContDiff ℝ 2
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

#print axioms p83_7d_velocity_contDiff_two

end Lanzarini
