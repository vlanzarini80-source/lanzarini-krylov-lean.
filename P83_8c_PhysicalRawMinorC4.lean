
import P83_8b_PhysicalKrylovC4
import P81_2b2_PhysicalMinorDerivative
import Mathlib

namespace Lanzarini

/-!
P83.8c: C4 regularity of the physical
raw Gram minor.

Derived from the physical Jacobi state
and velocity.

No P79.
No expected Taylor coefficients.
No sorry, admit, or new axioms.
-/

theorem p83_8c_rawMinor_contDiff_four
    (p q s delta : ℝ)
    (i j : Fin 4) :
    ContDiff ℝ 4
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t i j) := by

  have hs :
      ContDiff ℝ 4
        (p81_2_state p q s delta) :=
    p83_7g_state_contDiff_four
      p q s delta

  have hv :
      ContDiff ℝ 4
        (p81_2_velocity p q s delta) :=
    p83_8a_velocity_contDiff_four
      p q s delta

  have hsi :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2_state p q s delta t) i) := by
    fun_prop

  have hsj :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2_state p q s delta t) j) := by
    fun_prop

  have hvi :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2_velocity p q s delta t) i) := by
    fun_prop

  have hvj :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2_velocity p q s delta t) j) := by
    fun_prop

  have hminor :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2_state p q s delta t) i *
            (p81_2_velocity p q s delta t) j -
          (p81_2_state p q s delta t) j *
            (p81_2_velocity p q s delta t) i) :=
    (hsi.mul hvj).sub (hsj.mul hvi)

  simpa only [
    p81_2b2_rawMinor,
    krylovGramCoordinate
  ] using hminor

#print axioms p83_8c_rawMinor_contDiff_four

end Lanzarini
