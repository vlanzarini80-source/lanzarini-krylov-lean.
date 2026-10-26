
import P78_2_PhysicalSpeedResidual

namespace Lanzarini

/-!
P79: Local defect coefficient, r = 0.

Exact algebra of the fourth-order Taylor
jets of the two contributing Gram minors.

No sorry.
No admit.
No new axioms.

IMPORTANT:
The connection between these finite jets
and the derivatives of the actual Jacobi
evolution is a separate proof obligation.
This file does not assert that connection.
-/

/-- First local defect. -/
def p79_r0_omega
    (p q r : ℝ) : ℝ :=
  r ^ 2 - 3 * q ^ 2 + 3 * p ^ 2

/--
Fourth-order imaginary coefficient of
the Gram minor with indices (1,2).

The expression is assembled from the
lower Taylor coefficients of w and v.
-/
def p79_r0_minor12_jet
    (p q r : ℝ) : ℝ :=
  (-p) *
      (p * q * (p ^ 2 + q ^ 2 + r ^ 2) / 6)
  + (p * (7 * p ^ 2 + q ^ 2) / 6) *
      (-p * q)
  - (-p * q) *
      (p * (p ^ 2 + q ^ 2) / 2)
  - (p * q * (p ^ 2 + q ^ 2 + r ^ 2) / 12
      + p ^ 3 * q / 2) * (-p)

/-- Derive the first minor coefficient. -/
theorem p79_r0_minor12_formula
    (p q r : ℝ) :
    p79_r0_minor12_jet p q r =
      -(p ^ 2 * q * p79_r0_omega p q r) / 12 := by
  unfold p79_r0_minor12_jet
  unfold p79_r0_omega
  ring

/--
Fourth-order imaginary coefficient of
the Gram minor with indices (1,3).
-/
def p79_r0_minor13_jet
    (p q r delta : ℝ) : ℝ :=
  (-p) * (delta * p * q * r / 6)
  - (delta * p * q * r / 8) * (-p)

/-- Derive the diagonal-defect contribution. -/
theorem p79_r0_minor13_formula
    (p q r delta : ℝ) :
    p79_r0_minor13_jet p q r delta =
      -(delta * p ^ 2 * q * r) / 24 := by
  unfold p79_r0_minor13_jet
  ring

/--
Leading Gram coefficient assembled
from the two fourth-order minor jets.
-/
def p79_r0_gramJetCoefficient
    (p q r delta : ℝ) : ℝ :=
  (p79_r0_minor12_jet p q r) ^ 2 +
  (p79_r0_minor13_jet p q r delta) ^ 2

/--
Exact factorization, derived without
assuming the expected coefficient.
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
Normalize the Gram jet coefficient by
the leading denominator coefficient p^4.

A nonzero initial coupling is required.
-/
def p79_r0_deficitJetCoefficient
    (p q r delta : ℝ) : ℝ :=
  p79_r0_gramJetCoefficient p q r delta /
    p ^ 4

/--
Exact candidate coefficient of t^6,
derived from the finite Gram jets.

This is not yet a theorem about the
Taylor expansion of the actual D(t).
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
