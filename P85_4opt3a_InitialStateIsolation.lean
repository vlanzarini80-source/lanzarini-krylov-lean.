
import P84_4a_GeneralJacobiPowers

namespace Lanzarini

set_option maxHeartbeats 500000

/-!
P85.4 OPT3-A

Isolated initial state and physical matrix action.

No expected deficit coefficients.
No P79.
No additional axioms.
-/

noncomputable def p85_opt3_state
    (p q r d e f : ℝ) :
    ℕ → Fin 4 → ℂ
  | 0 => p81_e0
  | k + 1 =>
      ((-Complex.I) •
        p84_H p q r d e f).mulVec
          (p85_opt3_state p q r d e f k)


theorem p85_opt3_state_zero
    (p q r d e f : ℝ) :
    p85_opt3_state p q r d e f 0 =
      ![1, 0, 0, 0] := by

  rfl

#print axioms p85_opt3_state_zero


theorem p85_opt3_state_zero_components
    (p q r d e f : ℝ) :
    p85_opt3_state p q r d e f 0 0 = 1 ∧
    p85_opt3_state p q r d e f 0 1 = 0 ∧
    p85_opt3_state p q r d e f 0 2 = 0 ∧
    p85_opt3_state p q r d e f 0 3 = 0 := by

  simp [p85_opt3_state, p81_e0]

#print axioms p85_opt3_state_zero_components


theorem p85_opt3_generator_action
    (p q r d e f : ℝ)
    (x : Fin 4 → ℂ) :
    ((-Complex.I) •
      p84_H p q r d e f).mulVec x =
      ![
        -Complex.I * ((p : ℂ) * x 1),

        -Complex.I *
          ((p : ℂ) * x 0 +
           (d : ℂ) * x 1 +
           (q : ℂ) * x 2),

        -Complex.I *
          ((q : ℂ) * x 1 +
           (e : ℂ) * x 2 +
           (r : ℂ) * x 3),

        -Complex.I *
          ((r : ℂ) * x 2 +
           (f : ℂ) * x 3)
      ] := by

  ext i

  fin_cases i <;>
    simp [
      p84_H,
      p84_a,
      p84_b,
      jacobiComplex,
      jacobiReal,
      jacobiRealEntry,
      Matrix.mulVec,
      dotProduct,
      Fin.sum_univ_succ
    ] <;> ring

#print axioms p85_opt3_generator_action


theorem p85_opt3_state_one
    (p q r d e f : ℝ) :
    p85_opt3_state p q r d e f 1 =
      ![0, -Complex.I * (p : ℂ), 0, 0] := by

  rw [p85_opt3_state]
  rw [p85_opt3_generator_action]

  ext i

  fin_cases i <;>
    simp [p85_opt3_state, p81_e0]

#print axioms p85_opt3_state_one


theorem p85_opt3_state_two
    (p q r d e f : ℝ) :
    p85_opt3_state p q r d e f 2 =
      ![
        -((p : ℂ) ^ 2),
        -((d : ℂ) * (p : ℂ)),
        -((q : ℂ) * (p : ℂ)),
        0
      ] := by

  rw [p85_opt3_state]
  rw [p85_opt3_state_one]
  rw [p85_opt3_generator_action]

  ext i

  fin_cases i <;>
    simp [← mul_assoc, Complex.I_mul_I] <;>
    ring

#print axioms p85_opt3_state_two


theorem p85_opt3_state_power
    (p q r d e f : ℝ)
    (k : ℕ) :
    p85_opt3_state p q r d e f k =
      (((-Complex.I) •
        p84_H p q r d e f) ^ k).mulVec
          p81_e0 := by

  induction k with
  | zero =>
      simp [p85_opt3_state]

  | succ k ih =>
      rw [p85_opt3_state, ih]
      rw [Matrix.mulVec_mulVec]
      rw [pow_succ']

#print axioms p85_opt3_state_power


theorem p85_opt3_physical_bridge
    (p q r d e f : ℝ)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        jacobiState 4
          (p84_a d e f)
          (p84_b p q r)
          t p81_e0) 0 =
      p85_opt3_state p q r d e f k := by

  rw [p84_initial_derivatives]
  exact (p85_opt3_state_power
    p q r d e f k).symm

#print axioms p85_opt3_physical_bridge

end Lanzarini
