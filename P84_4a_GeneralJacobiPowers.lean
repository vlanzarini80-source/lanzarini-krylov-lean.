
import P81_1_JacobiPhysicalPowers

namespace Lanzarini

/-!
P84.4a: General four-site real Jacobi Hamiltonian.

Only structural identities derived from jacobiComplex.
No Taylor or deficit coefficient is assumed.
Candidate: requires Lean 4.24.0 / mathlib CI verification.
-/

noncomputable def p84_a (d e f : ℝ) : Fin 4 → ℝ :=
  ![0, d, e, f]

noncomputable def p84_b (p q r : ℝ) : Fin 4 → ℝ :=
  ![p, q, r, 0]

noncomputable def p84_H (p q r d e f : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  jacobiComplex 4 (p84_a d e f) (p84_b p q r)

/-- Matrix action computed from the Jacobi definition. -/
theorem p84_H_action (p q r d e f : ℝ) (x : Fin 4 → ℂ) :
    (p84_H p q r d e f).mulVec x =
      ![ (p : ℂ) * x 1,
         (p : ℂ) * x 0 + (d : ℂ) * x 1 + (q : ℂ) * x 2,
         (q : ℂ) * x 1 + (e : ℂ) * x 2 + (r : ℂ) * x 3,
         (r : ℂ) * x 2 + (f : ℂ) * x 3 ] := by
  ext i
  fin_cases i <;>
    simp [p84_H, p84_a, p84_b,
      jacobiComplex, jacobiReal, jacobiRealEntry,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- First physical matrix power, no coefficient supplied. -/
theorem p84_H1 (p q r d e f : ℝ) :
    (p84_H p q r d e f).mulVec p81_e0 =
      ![0, (p : ℂ), 0, 0] := by
  rw [p84_H_action]
  ext i
  fin_cases i <;> simp [p81_e0]

/-- Second physical matrix power, derived from H1. -/
theorem p84_H2 (p q r d e f : ℝ) :
    (p84_H p q r d e f).mulVec
      ((p84_H p q r d e f).mulVec p81_e0) =
      ![(p : ℂ) ^ 2,
        (d : ℂ) * (p : ℂ),
        (p : ℂ) * (q : ℂ),
        0] := by
  rw [p84_H1, p84_H_action]
  ext i
  fin_cases i <;> simp <;> ring

/-- True physical jets for the general matrix, not assumed Taylor data. -/
theorem p84_initial_derivatives (p q r d e f : ℝ) (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        jacobiState 4 (p84_a d e f) (p84_b p q r) t p81_e0) 0 =
      (((-Complex.I) • p84_H p q r d e f) ^ k).mulVec p81_e0 := by
  exact p80_1_initial_derivative
    4 (p84_a d e f) (p84_b p q r) p81_e0 k

#print axioms p84_H_action
#print axioms p84_H1
#print axioms p84_H2
#print axioms p84_initial_derivatives

end Lanzarini
