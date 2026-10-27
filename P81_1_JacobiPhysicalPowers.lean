
import P80_1_TrueEvolutionJets

namespace Lanzarini

/-!
P81.1: Physical Jacobi powers, r = 0.

The Hamiltonian is constructed from the
actual jacobiComplex definition.

No use of P79 coefficient formulas.
No assumed Gram-minor coefficients.
No sorry, admit, or new axioms.

Candidate requiring Lean CI verification.
-/

/-- Local diagonal entries after energy shift. -/
noncomputable def p81_a (delta : ℝ) :
    Fin 4 → ℝ :=
  ![0, 0, 0, delta]

/-- Three successive Jacobi couplings. -/
noncomputable def p81_b (p q s : ℝ) :
    Fin 4 → ℝ :=
  ![p, q, s, 0]

/-- Initial state localized at index zero. -/
noncomputable def p81_e0 : Fin 4 → ℂ :=
  ![1, 0, 0, 0]

/-- The actual four-dimensional Jacobi matrix. -/
noncomputable def p81_H
    (p q s delta : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  jacobiComplex 4
    (p81_a delta) (p81_b p q s)

/--
Direct matrix action, derived from
Jacobi entries, not from Taylor data.
-/
theorem p81_H_action
    (p q s delta : ℝ)
    (x : Fin 4 → ℂ) :
    (p81_H p q s delta).mulVec x =
      ![
        (p : ℂ) * x 1,
        (p : ℂ) * x 0 + (q : ℂ) * x 2,
        (q : ℂ) * x 1 + (s : ℂ) * x 3,
        (s : ℂ) * x 2 + (delta : ℂ) * x 3
      ] := by
  ext i
  fin_cases i <;>
    simp [
      p81_H, p81_a, p81_b,
      jacobiComplex, jacobiReal,
      jacobiRealEntry,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ
    ] <;> ring

/-- First application of H to e0. -/
theorem p81_H1
    (p q s delta : ℝ) :
    (p81_H p q s delta).mulVec p81_e0 =
      ![0, (p : ℂ), 0, 0] := by
  rw [p81_H_action]
  ext i
  fin_cases i <;> simp [p81_e0]

/-- Second application, obtained from H1. -/
theorem p81_H2
    (p q s delta : ℝ) :
    (p81_H p q s delta).mulVec
      ((p81_H p q s delta).mulVec p81_e0) =
      ![
        (p : ℂ) ^ 2,
        0,
        (p : ℂ) * (q : ℂ),
        0
      ] := by
  rw [p81_H1, p81_H_action]
  ext i
  fin_cases i <;> simp <;> ring

/-- Third application, obtained from H2. -/
theorem p81_H3
    (p q s delta : ℝ) :
    (p81_H p q s delta).mulVec
      ((p81_H p q s delta).mulVec
        ((p81_H p q s delta).mulVec p81_e0)) =
      ![
        0,
        (p : ℂ) *
          ((p : ℂ) ^ 2 + (q : ℂ) ^ 2),
        0,
        (p : ℂ) * (q : ℂ) * (s : ℂ)
      ] := by
  rw [p81_H2, p81_H_action]
  ext i
  fin_cases i <;> simp <;> ring

/-- Fourth application, obtained from H3. -/
theorem p81_H4
    (p q s delta : ℝ) :
    (p81_H p q s delta).mulVec
      ((p81_H p q s delta).mulVec
        ((p81_H p q s delta).mulVec
          ((p81_H p q s delta).mulVec
            p81_e0))) =
      ![
        (p : ℂ) ^ 2 *
          ((p : ℂ) ^ 2 + (q : ℂ) ^ 2),
        0,
        (p : ℂ) * (q : ℂ) *
          ((p : ℂ) ^ 2 +
            (q : ℂ) ^ 2 + (s : ℂ) ^ 2),
        (delta : ℂ) * (p : ℂ) *
          (q : ℂ) * (s : ℂ)
      ] := by
  rw [p81_H3, p81_H_action]
  ext i
  fin_cases i <;> simp <;> ring

/--
Physical time derivatives, independently
linked to P80.1 and to the same Jacobi H.

This theorem does not assume any
Taylor coefficient or deficit formula.
-/
theorem p81_true_initial_derivatives
    (p q s delta : ℝ)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        jacobiState 4
          (p81_a delta)
          (p81_b p q s)
          t p81_e0) 0 =
    (((-Complex.I) • p81_H p q s delta) ^ k).mulVec
      p81_e0 := by
  exact p80_1_initial_derivative
    4 (p81_a delta) (p81_b p q s)
    p81_e0 k

#print axioms p81_H_action
#print axioms p81_H1
#print axioms p81_H2
#print axioms p81_H3
#print axioms p81_H4
#print axioms p81_true_initial_derivatives

end Lanzarini
