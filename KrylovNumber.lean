
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
P56.4: The Krylov number operator
acts diagonally on every state.
-/
theorem krylovNumberOperator_mulVec
    (n : ℕ) (psi : Fin n → ℂ) :
    (krylovNumberOperator n).mulVec psi =
      fun j : Fin n => ((j.val : ℝ) : ℂ) * psi j := by
  funext j
  exact Matrix.mulVec_diagonal
    (fun k : Fin n => ((k.val : ℝ) : ℂ))
    psi j

/--
P56.5: The matrix expectation equals
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
  dsimp only
  rw [Complex.ofReal_mul]
  rw [Complex.normSq_eq_conj_mul_self]
  simp [mul_assoc, mul_comm, mul_left_comm]

/--
P56.6: Krylov complexity at time zero
equals its initial value.
-/
theorem krylovComplexityAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovComplexityAt n a b 0 psi =
      krylovComplexity psi := by
  unfold krylovComplexityAt
  rw [jacobiState_zero]

/--
P57.1: Krylov complexity is nonnegative
for every finite-dimensional complex state.

No normalization assumption is required.
-/
theorem krylovComplexity_nonneg
    {n : ℕ} (psi : Fin n → ℂ) :
    0 ≤ krylovComplexity psi := by
  unfold krylovComplexity
  apply Finset.sum_nonneg
  intro j hj
  positivity

/--
P57.2: Krylov complexity remains nonnegative
at every real time under Jacobi evolution.

No normalization assumption is required.
-/
theorem krylovComplexityAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    0 ≤ krylovComplexityAt n a b t psi := by
  unfold krylovComplexityAt
  exact krylovComplexity_nonneg
    (jacobiState n a b t psi)

end Lanzarini
