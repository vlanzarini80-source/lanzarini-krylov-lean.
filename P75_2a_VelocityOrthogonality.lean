
import P75_1_Orthogonality

namespace Lanzarini

/-!
P75.2a: Real orthogonality of the physical
Jacobi velocity.

No normalization hypothesis is required.
No sorry, admit, or additional axioms.
-/

/--
An anti-Hermitian matrix has purely imaginary
expectation values.
-/
theorem p75_antiHermitian_real_orthogonal
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ)
    (hA : A.conjTranspose = -A) :
    (jacobiInner v (A.mulVec v)).re = 0 := by

  have hstar :
      star (jacobiInner v (A.mulVec v)) =
        -jacobiInner v (A.mulVec v) := by

    unfold jacobiInner

    change
      star (dotProduct (star v) (A.mulVec v)) =
        -dotProduct (star v) (A.mulVec v)

    rw [star_dotProduct]
    rw [Matrix.star_mulVec]
    rw [Matrix.dotProduct_mulVec]
    rw [Matrix.vecMul_vecMul]

    rw [show star A = A.conjTranspose.transpose from rfl]
    rw [hA]

    simp

  have hre := congrArg Complex.re hstar

  simp only [
    Complex.star_def,
    Complex.conj_re,
    Complex.neg_re
  ] at hre

  linarith

/--
Real orthogonality of the Jacobi state
and its physical velocity -iH psi.
-/
theorem p75_state_velocity_real_orthogonal
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    (jacobiInner
      (jacobiState n a b t psi)
      (((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi))).re = 0 := by

  apply p75_antiHermitian_real_orthogonal

  rw [Matrix.conjTranspose_smul]
  rw [jacobiComplex_conjTranspose]

  simp [Complex.conj_I, neg_smul]

#print axioms p75_antiHermitian_real_orthogonal
#print axioms p75_state_velocity_real_orthogonal

end Lanzarini
