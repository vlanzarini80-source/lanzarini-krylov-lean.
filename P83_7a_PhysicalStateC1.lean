
import P83_6_PhysicalFrechetBridge
import Mathlib

namespace Lanzarini

/-!
P83.7a - Physical state C1 regularity.

Derived from the genuine Jacobi evolution.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_7a_state_contDiff_one
    (p q s delta : ℝ) :
    ContDiff ℝ 1
      (p81_2_state p q s delta) := by
  have hv :
      Continuous
        (p81_2_velocity p q s delta) :=
    (p83_5d_velocity_differentiable
      p q s delta).continuous
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨
    (fun t : ℝ =>
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        (p81_2_velocity p q s delta t)),
    ?_, ?_⟩
  · fun_prop
  · intro t
    exact
      (p81_2_state_hasDerivAt
        p q s delta t).hasFDerivAt

#print axioms p83_7a_state_contDiff_one

end Lanzarini
