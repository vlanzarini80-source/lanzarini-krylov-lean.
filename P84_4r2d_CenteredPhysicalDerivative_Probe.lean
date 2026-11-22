
import P84_4r2c_InitialKrylovZero_Probe

namespace Lanzarini

/-!
P84.4r2d: physical centered derivative.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4r2d_centered_hasDerivAt
    (p q r d e f : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun t : ℝ =>
        p84_4l_u p q r d e f t j)
      (p84_4l_v p q r d e f 0 j)
      0 := by

  have hf :=
    (p84_4r2b_real_centered_factor
      p q r d e f j).ofReal

  have hg :=
    p84_4r2a_psi_hasDerivAt
      p q r d e f j

  have hp := hf.mul hg

  have hK0 :=
    p84_4r2c_K_zero p q r d e f

  have hs :
      (j.val : ℂ) *
        p84_4l_v p q r d e f 0 j =
      p84_4l_v p q r d e f 0 j := by
    exact congrFun
      (p84_4r1_initial_velocity_support
        p q r d e f) j

  change HasDerivAt
    (fun t : ℝ =>
      (((j.val : ℝ) -
        p84_4c1_K p q r d e f t : ℝ) : ℂ) *
        p84_4l_psi p q r d e f t j)
    (p84_4l_v p q r d e f 0 j)
    0

  convert hp using 1
  simp [hK0, hs]

#print axioms p84_4r2d_centered_hasDerivAt

end Lanzarini
