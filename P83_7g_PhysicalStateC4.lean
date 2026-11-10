
import P83_7f_PhysicalVelocityC3
import Mathlib

namespace Lanzarini

/-!
P83.7g - Physical state C4 regularity.

Derived from the physical evolution
equation and C3 regularity of velocity.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_7g_state_contDiff_four
    (p q s delta : ℝ) :
    ContDiff ℝ 4
      (p81_2_state p q s delta) := by

  have hv :
      ContDiff ℝ 3
        (p81_2_velocity p q s delta) :=
    p83_7f_velocity_contDiff_three
      p q s delta

  let D : ℝ → (ℝ →L[ℝ] (Fin 4 → ℂ)) :=
    fun t =>
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        (p81_2_velocity p q s delta t)

  have hD : ContDiff ℝ 3 D := by
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
      (n := 3)).mpr
      ⟨D, hD, hderiv⟩

#print axioms p83_7g_state_contDiff_four

end Lanzarini
