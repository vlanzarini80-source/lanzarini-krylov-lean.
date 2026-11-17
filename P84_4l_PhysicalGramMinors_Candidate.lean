
import P84_4k_ExactPhysicalGramIdentity_Candidate

namespace Lanzarini

/-!
P84.4l: physical Gram minors.

The vectors are constructed from the actual
four-site Jacobi evolution.

No Taylor coefficients are assumed.
No P79.
No sorry, admit, or new axioms.
-/

/-- Physical state. -/
noncomputable def p84_4l_psi
    (p q r d e f t : ℝ) : Fin 4 → ℂ :=
  jacobiState 4
    (p84_a d e f)
    (p84_b p q r)
    t p81_e0

/-- Centered Krylov vector. -/
noncomputable def p84_4l_u
    (p q r d e f t : ℝ) : Fin 4 → ℂ :=
  krylovCenteredState
    (p84_4l_psi p q r d e f t)

/-- Centered physical energy channel. -/
noncomputable def p84_4l_v
    (p q r d e f t : ℝ) : Fin 4 → ℂ :=
  fun j =>
    -Complex.I *
      (p76_centeredEnergy 4
        (p84_a d e f)
        (p84_b p q r)
        (p84_4l_psi p q r d e f t)) j

/-- Physical Gram minor. -/
noncomputable def p84_4l_minor
    (p q r d e f t : ℝ)
    (i j : Fin 4) : ℂ :=
  krylovGramCoordinate
    (p84_4l_u p q r d e f t)
    (p84_4l_v p q r d e f t)
    i j

/-- Explicit determinant formula. -/
theorem p84_4l_minor_formula
    (p q r d e f t : ℝ)
    (i j : Fin 4) :
    p84_4l_minor p q r d e f t i j =
      p84_4l_u p q r d e f t i *
        p84_4l_v p q r d e f t j -
      p84_4l_u p q r d e f t j *
        p84_4l_v p q r d e f t i := by
  rfl

/-- Antisymmetry of the physical minors. -/
theorem p84_4l_minor_swap
    (p q r d e f t : ℝ)
    (i j : Fin 4) :
    p84_4l_minor p q r d e f t j i =
      -p84_4l_minor p q r d e f t i j := by
  exact krylovGramCoordinate_swap
    (p84_4l_u p q r d e f t)
    (p84_4l_v p q r d e f t)
    i j

/-- Diagonal minors vanish. -/
theorem p84_4l_minor_self
    (p q r d e f t : ℝ)
    (i : Fin 4) :
    p84_4l_minor p q r d e f t i i = 0 := by
  exact krylovGramCoordinate_self
    (p84_4l_u p q r d e f t)
    (p84_4l_v p q r d e f t)
    i

/-- Every physical minor has nonnegative norm square. -/
theorem p84_4l_minor_normSq_nonneg
    (p q r d e f t : ℝ)
    (i j : Fin 4) :
    0 ≤ Complex.normSq
      (p84_4l_minor p q r d e f t i j) := by
  exact Complex.normSq_nonneg _

/-- Physical Gram sum. -/
noncomputable def p84_4l_gramSum
    (p q r d e f t : ℝ) : ℝ :=
  krylovGramSum
    (p84_4l_u p q r d e f t)
    (p84_4l_v p q r d e f t)

/-- The physical Gram sum is nonnegative. -/
theorem p84_4l_gramSum_nonneg
    (p q r d e f t : ℝ) :
    0 ≤ p84_4l_gramSum p q r d e f t := by
  exact krylovGramSum_nonneg
    (p84_4l_u p q r d e f t)
    (p84_4l_v p q r d e f t)

#print axioms p84_4l_minor_formula
#print axioms p84_4l_minor_swap
#print axioms p84_4l_minor_self
#print axioms p84_4l_minor_normSq_nonneg
#print axioms p84_4l_gramSum_nonneg

end Lanzarini
