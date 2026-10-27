
import P78_2_PhysicalSpeedResidual

namespace Lanzarini

/-!
P79: Local defect coefficient, r = 0.

Exact algebra of fourth-order Gram minor jets.

The division-based definitions are explicitly
noncomputable, as required for real arithmetic.

No sorry.
No admit.
No new axioms.

This file proves algebraic identities only.
It does not yet establish the Taylor expansion
of the physical Jacobi evolution.
-/

/-- First local defect. -/
def p79_r0_omega
    (p q r : ℝ) : ℝ :=
  r ^ 2 - 3 * q ^ 2 + 3 * p ^ 2

/--
Fourth-order coefficient of the first
candidate Gram minor.
-/
noncomputable def p79_r0_minor12_jet
    (p q r : ℝ) : ℝ :=
  (-p) *
      (p * q * (p ^ 2 + q ^ 2 + r ^ 2) / 6)
  + (p * (7 * p ^ 2 + q ^ 2) / 6) *
      (-p * q)
  - (-p * q) *
      (p * (p ^ 2 + q ^ 2) / 2)
  - (p * q * (p ^ 2 + q ^ 2 + r ^ 2) / 12
      + p ^ 3 * q / 2) * (-p)

/-- Algebraic formula for the first jet. -/
theorem p79_r0_minor12_formula
    (p q r : ℝ) :
    p79_r0_minor12_jet p q r =
      -(p ^ 2 * q *
        p79_r0_omega p q r) / 12 := by
  unfold p79_r0_minor12_jet
  unfold p79_r0_omega
  ring

/--
Fourth-order coefficient of the second
candidate Gram minor.
-/
noncomputable def p79_r0_minor13_jet
    (p q r delta : ℝ) : ℝ :=
  (-p) * (delta * p * q * r / 6)
  - (delta * p * q * r / 8) * (-p)

/-- Algebraic formula for the second jet. -/
theorem p79_r0_minor13_formula
    (p q r delta : ℝ) :
    p79_r0_minor13_jet p q r delta =
      -(delta * p ^ 2 * q * r) / 24 := by
  unfold p79_r0_minor13_jet
  ring

/--
Sum of the two squared candidate
Gram-minor coefficients.
-/
noncomputable def p79_r0_gramJetCoefficient
    (p q r delta : ℝ) : ℝ :=
  (p79_r0_minor12_jet p q r) ^ 2 +
  (p79_r0_minor13_jet p q r delta) ^ 2

/--
Exact algebraic factorization.
No assumption of the target formula.
-/
theorem p79_r0_gramJet_formula
    (p q r delta : ℝ) :
    p79_r0_gramJetCoefficient p q r delta =
      p ^ 4 * q ^ 2 / 576 *
        (4 * (p79_r0_omega p q r) ^ 2
          + r ^ 2 * delta ^ 2) := by
  unfold p79_r0_gramJetCoefficient
  rw [p79_r0_minor12_formula]
  rw [p79_r0_minor13_formula]
  ring

/--
Normalize the coefficient by p^4.
This is an algebraic definition, not
yet the actual dynamical deficit limit.
-/
noncomputable def p79_r0_deficitJetCoefficient
    (p q r delta : ℝ) : ℝ :=
  p79_r0_gramJetCoefficient p q r delta /
    p ^ 4

/--
Exact normalized algebraic coefficient.
Requires the first coupling to be nonzero.
-/
theorem p79_r0_deficitJet_formula
    (p q r delta : ℝ)
    (hp : p ≠ 0) :
    p79_r0_deficitJetCoefficient
        p q r delta =
      q ^ 2 / 576 *
        (4 * (p79_r0_omega p q r) ^ 2
          + r ^ 2 * delta ^ 2) := by
  unfold p79_r0_deficitJetCoefficient
  rw [p79_r0_gramJet_formula]
  apply (div_eq_iff (pow_ne_zero 4 hp)).2
  ring

#print axioms p79_r0_minor12_formula
#print axioms p79_r0_minor13_formula
#print axioms p79_r0_gramJet_formula
#print axioms p79_r0_deficitJet_formula

end Lanzarini
