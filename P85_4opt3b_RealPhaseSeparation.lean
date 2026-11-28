
import P85_4opt3a_InitialStateIsolation

namespace Lanzarini

set_option maxHeartbeats 500000
set_option maxRecDepth 1024

/-!
P85.4 OPT3-B

Real polynomial state recursion.
Exact complex phase separation.
Physical evolution bridge.

No expected deficit coefficients.
No additional hypotheses.
No additional axioms.
No P79.
-/

noncomputable def p85_opt3b_realStep
    (p q r d e f : ℝ)
    (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![
    p * x 1,
    p * x 0 + d * x 1 + q * x 2,
    q * x 1 + e * x 2 + r * x 3,
    r * x 2 + f * x 3
  ]

noncomputable def p85_opt3b_realState
    (p q r d e f : ℝ) :
    ℕ → Fin 4 → ℝ
  | 0 => ![1, 0, 0, 0]
  | k + 1 =>
      p85_opt3b_realStep p q r d e f
        (p85_opt3b_realState p q r d e f k)

theorem p85_opt3b_real_zero
    (p q r d e f : ℝ) :
    p85_opt3b_realState p q r d e f 0 =
      ![1, 0, 0, 0] := by
  rfl

#print axioms p85_opt3b_real_zero

theorem p85_opt3b_real_succ
    (p q r d e f : ℝ)
    (k : ℕ) :
    p85_opt3b_realState p q r d e f (k + 1) =
      p85_opt3b_realStep p q r d e f
        (p85_opt3b_realState p q r d e f k) := by
  rfl

#print axioms p85_opt3b_real_succ

theorem p85_opt3b_generator_phase
    (p q r d e f : ℝ)
    (c : ℂ)
    (x : Fin 4 → ℝ) :
    ((-Complex.I) •
      p84_H p q r d e f).mulVec
        (fun j => c * (x j : ℂ)) =
      (fun j =>
        (-Complex.I * c) *
          (p85_opt3b_realStep
            p q r d e f x j : ℂ)) := by

  rw [p85_opt3_generator_action]

  funext j

  fin_cases j <;>
    simp [p85_opt3b_realStep] <;>
    push_cast <;>
    ring

#print axioms p85_opt3b_generator_phase

theorem p85_opt3b_phase_separation
    (p q r d e f : ℝ)
    (k : ℕ) :
    p85_opt3_state p q r d e f k =
      (fun j =>
        (-Complex.I) ^ k *
          (p85_opt3b_realState
            p q r d e f k j : ℂ)) := by

  induction k with

  | zero =>
      rw [p85_opt3_state_zero]

      funext j

      fin_cases j <;>
        simp [p85_opt3b_realState]

  | succ k ih =>
      rw [p85_opt3_state]
      rw [ih]
      rw [p85_opt3b_generator_phase]

      funext j

      rw [p85_opt3b_real_succ]
      rw [pow_succ']

#print axioms p85_opt3b_phase_separation

theorem p85_opt3b_physical_phase
    (p q r d e f : ℝ)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        jacobiState 4
          (p84_a d e f)
          (p84_b p q r)
          t p81_e0) 0 =
      (fun j =>
        (-Complex.I) ^ k *
          (p85_opt3b_realState
            p q r d e f k j : ℂ)) := by

  rw [p85_opt3_physical_bridge]
  exact p85_opt3b_phase_separation
    p q r d e f k

#print axioms p85_opt3b_physical_phase

theorem p85_opt3b_real_one
    (p q r d e f : ℝ) :
    p85_opt3b_realState p q r d e f 1 =
      ![0, p, 0, 0] := by

  funext j

  fin_cases j <;>
    simp [
      p85_opt3b_realState,
      p85_opt3b_realStep
    ]

#print axioms p85_opt3b_real_one

theorem p85_opt3b_real_two
    (p q r d e f : ℝ) :
    p85_opt3b_realState p q r d e f 2 =
      ![p ^ 2, d * p, q * p, 0] := by

  rw [p85_opt3b_real_succ]
  rw [p85_opt3b_real_one]

  funext j

  fin_cases j <;>
    simp [p85_opt3b_realStep] <;>
    ring

#print axioms p85_opt3b_real_two

end Lanzarini
