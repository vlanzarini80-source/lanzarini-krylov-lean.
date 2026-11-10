
import P83_7d_PhysicalVelocityC2
import Mathlib

namespace Lanzarini

/-!
P83.7e - Physical state C3 regularity.

Derive C3 regularity of the physical
Jacobi state from:

1. The physical evolution equation.
2. The already proved C2 regularity
   of the physical velocity.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.

This theorem does not establish C4
regularity or any deficit coefficient.
-/

theorem p83_7e_state_contDiff_three
    (p q s delta : ℝ) :
    ContDiff ℝ 3
      (p81_2_state p q s delta) := by

  have hv :
      ContDiff ℝ 2
        (p81_2_velocity p q s delta) :=
    p83_7d_velocity_contDiff_two
      p q s delta

  let D : ℝ → (ℝ →L[ℝ] (Fin 4 → ℂ)) :=
    fun t =>
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        (p81_2_velocity p q s delta t)

  have hD : ContDiff ℝ 2 D := by
    dsimp [D]
    fun_prop

  have hderiv :
      ∀ t : ℝ,
        HasFDerivAt
          (p81_2_state p q s delta)
          (D t) t := by
    intro t
    exact
      (p81_2_state_hasDerivAt
        p q s delta t).hasFDerivAt

  exact
    (contDiff_succ_iff_hasFDerivAt
      (n := 2)).mpr
      ⟨D, hD, hderiv⟩

#print axioms p83_7e_state_contDiff_three

end Lanzarini
