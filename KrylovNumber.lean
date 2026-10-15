
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
P57.1: Nonnegativity of Krylov complexity.

No normalization assumption is required.
-/
theorem krylovComplexity_nonneg
    {n : ℕ} (psi : Fin n → ℂ) :
    0 ≤ krylovComplexity psi := by
  unfold krylovComplexity
  apply Finset.sum_nonneg
  intro j hj
  have hindex : (0 : ℝ) ≤ (j.val : ℝ) :=
    Nat.cast_nonneg _
  have hnorm : 0 ≤ Complex.normSq (psi j) :=
    Complex.normSq_nonneg _
  exact mul_nonneg hindex hnorm

/--
P57.2: Nonnegativity at every real time
under Jacobi quantum evolution.

No normalization assumption is required.
-/
theorem krylovComplexityAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    0 ≤ krylovComplexityAt n a b t psi := by
  unfold krylovComplexityAt
  exact krylovComplexity_nonneg
    (jacobiState n a b t psi)

/--
P58.1: Second moment of the Krylov
number distribution.

No normalization assumption is required.
-/
noncomputable def krylovSecondMoment
    {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  ∑ j : Fin n,
    ((j.val : ℝ) ^ 2) * Complex.normSq (psi j)

/--
P58.2: Second moment under Jacobi evolution.
-/
noncomputable def krylovSecondMomentAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  krylovSecondMoment (jacobiState n a b t psi)

/--
P58.3: The second moment is nonnegative
for every finite-dimensional complex state.
-/
theorem krylovSecondMoment_nonneg
    {n : ℕ} (psi : Fin n → ℂ) :
    0 ≤ krylovSecondMoment psi := by
  unfold krylovSecondMoment
  apply Finset.sum_nonneg
  intro j hj
  have hindex : (0 : ℝ) ≤ (j.val : ℝ) ^ 2 :=
    sq_nonneg _
  have hnorm : 0 ≤ Complex.normSq (psi j) :=
    Complex.normSq_nonneg _
  exact mul_nonneg hindex hnorm

/--
P58.4: The evolved second moment
is nonnegative at every real time.
-/
theorem krylovSecondMomentAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    0 ≤ krylovSecondMomentAt n a b t psi := by
  unfold krylovSecondMomentAt
  exact krylovSecondMoment_nonneg
    (jacobiState n a b t psi)

/--
P58.5: At time zero, the second moment
equals its initial value.
-/
theorem krylovSecondMomentAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovSecondMomentAt n a b 0 psi =
      krylovSecondMoment psi := by
  unfold krylovSecondMomentAt
  rw [jacobiState_zero]

/--
P59.1: Krylov variance expression.

For normalized states, this is the variance
of the Krylov number distribution.

For unnormalized states, nonnegativity
is not asserted.
-/
noncomputable def krylovVariance
    {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  krylovSecondMoment psi -
    (krylovComplexity psi) ^ 2

/--
P59.2: Krylov variance expression
under Jacobi evolution.
-/
noncomputable def krylovVarianceAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  krylovVariance (jacobiState n a b t psi)

/--
P59.3: At time zero, the variance
expression equals its initial value.
-/
theorem krylovVarianceAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovVarianceAt n a b 0 psi =
      krylovVariance psi := by
  unfold krylovVarianceAt
  rw [jacobiState_zero]

/--
P59.4: Normalization is preserved
under Jacobi quantum evolution.
-/
theorem jacobiState_normalized
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    jacobiNormSq (jacobiState n a b t psi) = 1 := by
  rw [jacobiNormSq_state]
  exact hnorm

end Lanzarini
