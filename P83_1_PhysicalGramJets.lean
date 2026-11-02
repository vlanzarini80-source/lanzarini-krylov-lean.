
import P82_7_InitialResidualCancellation

namespace Lanzarini

/-!
P83.1: Physical Jacobi data for Gram jets.

This first stage extracts physical Hamiltonian
power coordinates from the existing P81 results.

No coefficient from P79 is imported.
No desired deficit formula is assumed.
-/

/--
The third Hamiltonian power reaches the
third site through three consecutive edges.
-/
theorem p83_1_third_power_site3
    (p q s delta : ℝ) :
    ((p81_H p q s delta).mulVec
      ((p81_H p q s delta).mulVec
        ((p81_H p q s delta).mulVec
          p81_e0))) 3 =
      (p : ℂ) * (q : ℂ) * (s : ℂ) := by
  rw [p81_H3]
  rfl

/--
At fourth order, the diagonal entry at
site three contributes to the physical
Hamiltonian power.
-/
theorem p83_1_fourth_power_site3
    (p q s delta : ℝ) :
    ((p81_H p q s delta).mulVec
      ((p81_H p q s delta).mulVec
        ((p81_H p q s delta).mulVec
          ((p81_H p q s delta).mulVec
            p81_e0)))) 3 =
      (delta : ℂ) *
        (p : ℂ) * (q : ℂ) * (s : ℂ) := by
  rw [p81_H4]
  rfl

/--
The fourth power at the second site
depends on the three couplings but
not on the diagonal defect.
-/
theorem p83_1_fourth_power_site2
    (p q s delta : ℝ) :
    ((p81_H p q s delta).mulVec
      ((p81_H p q s delta).mulVec
        ((p81_H p q s delta).mulVec
          ((p81_H p q s delta).mulVec
            p81_e0)))) 2 =
      (p : ℂ) * (q : ℂ) *
        ((p : ℂ) ^ 2 +
          (q : ℂ) ^ 2 +
          (s : ℂ) ^ 2) := by
  rw [p81_H4]
  rfl

#print axioms p83_1_third_power_site3
#print axioms p83_1_fourth_power_site3
#print axioms p83_1_fourth_power_site2

end Lanzarini
