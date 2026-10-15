
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
