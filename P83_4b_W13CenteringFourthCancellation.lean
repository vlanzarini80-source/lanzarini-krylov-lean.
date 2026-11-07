
import P83_3_CenteredGramDerivativeBridge
import P83_LocalFourthCancellation_Candidate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Lanzarini

/-!
P83.4b: Fourth-order cancellation of
physical W13 centering.

The original seven hypotheses are preserved.
The proof uses the independently verified
local fourth-order product cancellation.

No P79.
No assumed fourth-order coefficient.
No sorry, admit, or new axioms.
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

  exact p83_local_fourth_product_zero
    (fun t : ℝ =>
      (p81_2b3_K p q s delta t : ℂ))
    (fun t : ℝ =>
      p81_2b2_rawMinor
        p q s delta t 1 3)
    hK hR hK0 hK1 hR0 hR1 hR2

#print axioms p83_4b_w13_centering_fourth_zero

end Lanzarini
