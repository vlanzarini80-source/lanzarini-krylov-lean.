
import P83_2_PhysicalMinorAcceleration
import P82_4a_PhysicalResidual
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Lanzarini

/-!
P83: Physical initial cancellations.

All identities are derived from the
actual Jacobi evolution and previously
proved physical derivative theorems.

No P79 coefficient imported.
No desired deficit coefficient assumed.
No additional axioms.
Candidate requiring CI verification.
-/

/-- Initial physical Krylov complexity. -/
theorem p83_physical_K_zero
    (p q s delta : ℝ) :
    iteratedDeriv 0
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ))
      0 = 0 := by

  change
    (p81_2b3_K p q s delta 0 : ℂ) = 0

  change
    (krylovComplexity
      (p81_2_state p q s delta 0) : ℂ) = 0

  rw [p81_2b_state_zero]
  rw [p81_2b_initial_krylov_zero]
  norm_num

/--
The first physical Krylov derivative
vanishes at the initial basis state.
-/
theorem p83_physical_K_first_zero
    (p q s delta : ℝ) :
    iteratedDeriv 1
      (fun t : ℝ =>
        (p81_2b3_K p q s delta t : ℂ))
      0 = 0 := by

  have hz :
      p82_4a_Kdot p q s delta 0 = 0 := by
    simp [
      p82_4a_Kdot,
      p81_2b_state_zero,
      p81_e0,
      Fin.sum_univ_succ
    ]

  have hr :
      HasDerivAt
        (p81_2b3_K p q s delta)
        0 0 := by
    simpa only [hz] using
      (p82_4a_K_derivative
        p q s delta 0)

  have hc := hr.ofReal_comp

  simpa only [iteratedDeriv_one] using
    hc.deriv

/--
The physical raw Gram minor (1,3)
vanishes at the initial Jacobi state.
-/
theorem p83_physical_R13_zero
    (p q s delta : ℝ) :
    iteratedDeriv 0
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3)
      0 = 0 := by

  change
    p81_2b2_rawMinor
      p q s delta 0 1 3 = 0

  simp [
    p81_2b2_rawMinor,
    krylovGramCoordinate,
    p81_2b_state_zero,
    p81_e0
  ]

/--
The first derivative of the physical
raw minor (1,3) vanishes initially.
-/
theorem p83_physical_R13_first_zero
    (p q s delta : ℝ) :
    iteratedDeriv 1
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3)
      0 = 0 := by

  simpa only [iteratedDeriv_one] using
    (p83_2_rawMinor13_initial_derivative
      p q s delta).deriv

#print axioms p83_physical_K_zero
#print axioms p83_physical_K_first_zero
#print axioms p83_physical_R13_zero
#print axioms p83_physical_R13_first_zero

end Lanzarini
