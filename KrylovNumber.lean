
import Mathlib
import MatrixExpProbe

namespace Lanzarini

/--
P56.1: Krylov number operator.

The diagonal entries are 0, 1, ..., n-1.
-/
noncomputable def krylovNumberOperator
    (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal
    (fun j : Fin n => ((j.val : ℝ) : ℂ))

/--
P56.2: Krylov complexity as a finite sum.

No normalization assumption is required.
-/
noncomputable def krylovComplexity
    {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  ∑ j : Fin n,
    (j.val : ℝ) * Complex.normSq (psi j)

/--
P56.3: Krylov complexity of the evolved state.
-/
noncomputable def krylovComplexityAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  krylovComplexity (jacobiState n a b t psi)

/--
P56.4: The number operator acts diagonally.
-/
theorem krylovNumberOperator_mulVec
    (n : ℕ) (psi : Fin n → ℂ) :
    (krylovNumberOperator n).mulVec psi =
      fun j : Fin n => ((j.val : ℝ) : ℂ) * psi j := by
  simp [krylovNumberOperator, Matrix.diagonal_mulVec]

/--
P56.5: Matrix expectation equals
the explicit Krylov complexity sum.
-/
theorem krylovComplexity_expectation
    {n : ℕ} (psi : Fin n → ℂ) :
    jacobiInner psi
      ((krylovNumberOperator n).mulVec psi) =
        (krylovComplexity psi : ℂ) := by
  rw [krylovNumberOperator_mulVec]
  unfold jacobiInner krylovComplexity
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.ofReal_mul]
  rw [← Complex.normSq_eq_conj_mul_self]
  ring

/--
P56.6: At time zero, the Krylov complexity
equals its initial value.
-/
theorem krylovComplexityAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovComplexityAt n a b 0 psi =
      krylovComplexity psi := by
  unfold krylovComplexityAt
  rw [jacobiState_zero]

end Lanzarini
