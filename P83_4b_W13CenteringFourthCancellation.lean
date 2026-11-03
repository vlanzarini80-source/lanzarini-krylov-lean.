
import P83_3_CenteredGramDerivativeBridge
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Lanzarini

/-!
P83.4b: Fourth-order cancellation of
physical W13 centering.

The theorem uses explicitly stated
lower-order jets and smoothness.

No P79 coefficient is imported.
No fourth-order coefficient is assumed.
-/

/--
The fourth derivative of the physical
centering correction vanishes provided
the required lower-order jets vanish.

The physical verification of these
hypotheses remains a separate obligation.
-/
theorem p83_4b_w13_centering_fourth_zero
    (p q s delta : ℝ)
    (hK : ContDiffAt ℝ 4
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ)) 0)
    (hR : ContDiffAt ℝ 4
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3) 0)
    (hK0 : iteratedDeriv 0
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ)) 0 = 0)
    (hK1 : iteratedDeriv 1
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ)) 0 = 0)
    (hR0 : iteratedDeriv 0
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3) 0 = 0)
    (hR1 : iteratedDeriv 1
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3) 0 = 0)
    (hR2 : iteratedDeriv 2
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3) 0 = 0) :
    iteratedDeriv 4
      (fun t : ℝ =>
        p83_3_centerCorrection
          p q s delta t 1 3) 0 = 0 := by

  change
    iteratedDeriv 4
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ) *
          p81_2b2_rawMinor
            p q s delta t 1 3) 0 = 0

  rw [iteratedDeriv_fun_mul hK hR]

  norm_num [
    Finset.sum_range_succ,
    hK0, hK1,
    hR0, hR1, hR2
  ]

#print axioms p83_4b_w13_centering_fourth_zero

end Lanzarini
