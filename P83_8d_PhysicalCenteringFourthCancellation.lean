
import P83_8c_PhysicalRawMinorC4
import P83_5a_PhysicalCenteringBridge_Candidate
import Mathlib

namespace Lanzarini

/-!
P83.8d: Physical fourth-order centering cancellation.

The two regularity hypotheses of P83.5a
are derived from the physical Jacobi evolution.

No P79.
No expected Taylor coefficients.
No sorry, admit, or new axioms.

STATUS: Candidate pending explicit Lean compilation
and axiom audit.
-/

theorem p83_8d_physical_centering_fourth_zero
    (p q s delta : ℝ) :
    iteratedDeriv 4
      (fun t : ℝ =>
        p83_3_centerCorrection
          p q s delta t 1 3) 0 = 0 := by

  have hKreal :
      ContDiff ℝ 4
        (p81_2b3_K p q s delta) :=
    p83_8b_K_contDiff_four
      p q s delta

  have hKcomplex :
      ContDiff ℝ 4
        (fun t : ℝ =>
          (p81_2b3_K p q s delta t : ℂ)) := by
    fun_prop

  have hK :
      ContDiffAt ℝ 4
        (fun t : ℝ =>
          (p81_2b3_K p q s delta t : ℂ)) 0 :=
    hKcomplex.contDiffAt

  have hRglobal :
      ContDiff ℝ 4
        (fun t : ℝ =>
          p81_2b2_rawMinor
            p q s delta t 1 3) :=
    p83_8c_rawMinor_contDiff_four
      p q s delta 1 3

  have hR :
      ContDiffAt ℝ 4
        (fun t : ℝ =>
          p81_2b2_rawMinor
            p q s delta t 1 3) 0 :=
    hRglobal.contDiffAt

  exact
    p83_5a_physical_centering_fourth_zero
      p q s delta hK hR

#print axioms p83_8d_physical_centering_fourth_zero

end Lanzarini
