
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

/--
P60.1: Centered second-moment identity.

For a normalized state, Krylov variance
equals a sum of squared deviations.
-/
theorem krylovVariance_centered
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    krylovVariance psi =
      ∑ j : Fin n,
        ((j.val : ℝ) - krylovComplexity psi) ^ 2 *
          Complex.normSq (psi j) := by
  let m : ℝ := krylovComplexity psi
  let p : Fin n → ℝ := fun j => Complex.normSq (psi j)

  have hp : (∑ j : Fin n, p j) = 1 := by
    exact hnorm

  have hm :
      (∑ j : Fin n, (j.val : ℝ) * p j) = m := by
    rfl

  have hsecond :
      (∑ j : Fin n, ((j.val : ℝ) ^ 2) * p j) =
        krylovSecondMoment psi := by
    rfl

  have hexpand :
      (∑ j : Fin n,
        ((j.val : ℝ) - m) ^ 2 * p j) =
      (∑ j : Fin n, ((j.val : ℝ) ^ 2) * p j) -
        2 * m * (∑ j : Fin n, (j.val : ℝ) * p j) +
        m ^ 2 * (∑ j : Fin n, p j) := by
    calc
      _ = ∑ j : Fin n,
          (((j.val : ℝ) ^ 2) * p j -
            (2 * m) * ((j.val : ℝ) * p j) +
            (m ^ 2) * p j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = _ := by
        simp only [
          Finset.sum_add_distrib,
          Finset.sum_sub_distrib,
          ← Finset.mul_sum
        ]
        all_goals ring

  rw [hexpand, hp, hm, hsecond]

  change krylovSecondMoment psi -
      (krylovComplexity psi) ^ 2 =
    krylovSecondMoment psi -
      2 * m * m + m ^ 2 * 1

  dsimp [m]
  ring

/--
P60.2: Nonnegativity of Krylov variance
for every normalized complex state.
-/
theorem krylovVariance_nonneg
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    0 ≤ krylovVariance psi := by
  rw [krylovVariance_centered psi hnorm]
  apply Finset.sum_nonneg
  intro j hj
  have hsquare :
      0 ≤ ((j.val : ℝ) - krylovComplexity psi) ^ 2 :=
    sq_nonneg _
  have hweight :
      0 ≤ Complex.normSq (psi j) :=
    Complex.normSq_nonneg _
  exact mul_nonneg hsquare hweight

/--
P60.3: Nonnegativity of Krylov variance
at every real time under Jacobi evolution,
assuming a normalized initial state.
-/
theorem krylovVarianceAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    0 ≤ krylovVarianceAt n a b t psi := by
  unfold krylovVarianceAt
  apply krylovVariance_nonneg
  exact jacobiState_normalized n a b t psi hnorm

/--
P61.1: Characterization of zero Krylov variance
through the centered second-moment sum.

The state must be normalized.
-/
theorem krylovVariance_eq_zero_iff_centered
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    krylovVariance psi = 0 ↔
      (∑ j : Fin n,
        ((j.val : ℝ) - krylovComplexity psi) ^ 2 *
          Complex.normSq (psi j)) = 0 := by
  rw [krylovVariance_centered psi hnorm]

/--
P61.2: Centered variance identity
at every real time for normalized initial states.
-/
theorem krylovVarianceAt_centered
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    krylovVarianceAt n a b t psi =
      ∑ j : Fin n,
        ((j.val : ℝ) -
          krylovComplexity (jacobiState n a b t psi)) ^ 2 *
          Complex.normSq (jacobiState n a b t psi j) := by
  unfold krylovVarianceAt
  exact krylovVariance_centered
    (jacobiState n a b t psi)
    (jacobiState_normalized n a b t psi hnorm)

/--
P61.3: Zero variance at time t is equivalent
to the vanishing of the centered sum.
-/
theorem krylovVarianceAt_eq_zero_iff_centered
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    krylovVarianceAt n a b t psi = 0 ↔
      (∑ j : Fin n,
        ((j.val : ℝ) -
          krylovComplexity (jacobiState n a b t psi)) ^ 2 *
          Complex.normSq (jacobiState n a b t psi j)) = 0 := by
  rw [krylovVarianceAt_centered n a b t psi hnorm]

/--
P62.1: If the normalized Krylov variance vanishes,
then every centered weighted term vanishes.

No concentration assumption is introduced.
-/
theorem krylovVariance_zero_term
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1)
    (hzero : krylovVariance psi = 0)
    (j : Fin n) :
    ((j.val : ℝ) - krylovComplexity psi) ^ 2 *
      Complex.normSq (psi j) = 0 := by

  have hsum :
      (∑ k : Fin n,
        ((k.val : ℝ) - krylovComplexity psi) ^ 2 *
          Complex.normSq (psi k)) = 0 := by
    rw [← krylovVariance_centered psi hnorm]
    exact hzero

  have hnonneg (k : Fin n) :
      0 ≤ ((k.val : ℝ) - krylovComplexity psi) ^ 2 *
        Complex.normSq (psi k) :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

  have hle :
      ((j.val : ℝ) - krylovComplexity psi) ^ 2 *
        Complex.normSq (psi j) ≤
      ∑ k : Fin n,
        ((k.val : ℝ) - krylovComplexity psi) ^ 2 *
          Complex.normSq (psi k) := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (fun k hk => hnonneg k)
      (Finset.mem_univ j)

  rw [hsum] at hle
  exact le_antisymm hle (hnonneg j)

/--
P62.2: Zero variance forces zero probability
at every index different from the mean.

The conclusion is derived, not assumed.
-/
theorem krylovVariance_zero_off_mean
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1)
    (hzero : krylovVariance psi = 0)
    (j : Fin n)
    (hne : (j.val : ℝ) ≠ krylovComplexity psi) :
    Complex.normSq (psi j) = 0 := by

  have hterm :=
    krylovVariance_zero_term psi hnorm hzero j

  have hdiff :
      (j.val : ℝ) - krylovComplexity psi ≠ 0 :=
    sub_ne_zero.mpr hne

  have hsq :
      ((j.val : ℝ) - krylovComplexity psi) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hdiff

  exact (mul_eq_zero.mp hterm).resolve_left hsq

end Lanzarini
