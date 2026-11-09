
import P83_7a_PhysicalStateC1
import Mathlib

namespace Lanzarini

/-!
P83.7b - Physical velocity C1 regularity.

The physical acceleration is derived
from the constant Jacobi generator.

No P79.
No Taylor coefficient assumptions.
No sorry, admit, or new axioms.
-/

theorem p83_7b_velocity_contDiff_one
    (p q s delta : ℝ) :
    ContDiff ℝ 1
      (p81_2_velocity p q s delta) := by

  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    p81_2b1_generator p q s delta

  let acceleration : ℝ → Fin 4 → ℂ :=
    fun t =>
      A.mulVec
        (p81_2_velocity p q s delta t)

  have ha : Continuous acceleration := by
    let L :
        (Fin 4 → ℂ) →ₗ[ℝ] (Fin 4 → ℂ) :=
      (Matrix.mulVecBilin ℝ ℝ) A

    let LC :
        (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) :=
      LinearMap.toContinuousLinearMap L

    have hv :
        Continuous
          (p81_2_velocity p q s delta) :=
      (p83_5d_velocity_differentiable
        p q s delta).continuous

    exact LC.continuous.comp hv

  apply contDiff_one_iff_hasFDerivAt.mpr

  refine ⟨
    (fun t : ℝ =>
      ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ)
        (acceleration t)),
    ?_, ?_⟩

  · fun_prop

  · intro t
    exact
      (p81_2b1_velocity_hasDerivAt
        p q s delta t).hasFDerivAt

#print axioms p83_7b_velocity_contDiff_one

end Lanzarini
