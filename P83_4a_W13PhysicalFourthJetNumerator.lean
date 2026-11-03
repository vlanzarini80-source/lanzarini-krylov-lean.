
import P83_1_PhysicalGramJets

namespace Lanzarini

/-!
P83.4a: Physical fourth-jet contribution
for the W13 Gram channel.

The Hamiltonian powers come from the
actual Jacobi matrix.

No P79 coefficient is imported.
No target coefficient is assumed.
-/

theorem p83_4a_w13_fourth_jet_numerator
    (p q s delta : ℝ) :
    (4 : ℂ) * (-Complex.I * (p : ℂ)) *
        ((p81_H p q s delta).mulVec
          ((p81_H p q s delta).mulVec
            ((p81_H p q s delta).mulVec
              ((p81_H p q s delta).mulVec
                p81_e0)))) 3 -
      (3 : ℂ) *
        ((p81_H p q s delta).mulVec
          ((p81_H p q s delta).mulVec
            ((p81_H p q s delta).mulVec
              ((p81_H p q s delta).mulVec
                p81_e0)))) 3 *
        (-Complex.I * (p : ℂ)) =
      -Complex.I * (delta : ℂ) *
        (p : ℂ) ^ 2 *
        (q : ℂ) * (s : ℂ) := by
  simp_rw [p83_1_fourth_power_site3]
  ring

#print axioms p83_4a_w13_fourth_jet_numerator

end Lanzarini
