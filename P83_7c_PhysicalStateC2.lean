
import P83_7b_PhysicalVelocityC1
import Mathlib

namespace Lanzarini

/-!
P83.7c - Physical state C2 regularity.

C2 regularity of the physical Jacobi state,
derived from the physical evolution equation
and the C1 regularity of physical velocity.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_7c_state_contDiff_two
    (p q s delta : ℝ) :
    ContDiff ℝ 2
      (p81_2_state p q s delta) := by

  have hv :
      ContDiff ℝ 1
        (p81_2_velocity p q s delta) :=
    p83_7b_velocity_contDiff_one
      p q s delta

  let D : ℝ → (ℝ →L[ℝ] (Fin 4 → ℂ)) :=
    fun t =>
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        (p81_2_velocity p q s delta t)

  have hD : ContDiff ℝ 1 D := by
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
      (n := 1)).mpr
      ⟨D, hD, hderiv⟩

#print axioms p83_7c_state_contDiff_two

end Lanzarini
