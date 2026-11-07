
import P83_4b_W13CenteringFourthCancellation
import P83_R13SecondPhysicalZero_Candidate

namespace Lanzarini

/-!
P83.5a: Physical initial-data bridge.

The five initial vanishing jets are derived
from previously verified physical theorems.

Only two local C^4 regularity hypotheses
remain explicit.

No P79.
No expected physical coefficient.
No sorry, admit, or new axioms.

STATUS: Candidate. Requires CI compilation.
-/

/--
Physical W13 centering cancellation,
using the already established initial
Jacobi data.

The two remaining ContDiffAt assumptions
must be proved independently from the
actual physical evolution.
-/
theorem p83_5a_physical_centering_fourth_zero
    (p q s delta : ℝ)
    (hK : ContDiffAt ℝ 4
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ)) 0)
    (hR : ContDiffAt ℝ 4
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3) 0) :
    iteratedDeriv 4
      (fun t : ℝ =>
        p83_3_centerCorrection
          p q s delta t 1 3) 0 = 0 := by

  exact
    p83_4b_w13_centering_fourth_zero
      p q s delta
      hK
      hR
      (p83_physical_K_zero
        p q s delta)
      (p83_physical_K_first_zero
        p q s delta)
      (p83_physical_R13_zero
        p q s delta)
      (p83_physical_R13_first_zero
        p q s delta)
      (p83_physical_R13_second_zero
        p q s delta)

#print axioms p83_5a_physical_centering_fourth_zero

end Lanzarini
