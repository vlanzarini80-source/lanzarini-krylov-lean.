
import Mathlib
import MatrixExpProbe

namespace Lanzarini

/-- P56.1: Krylov number operator. -/
noncomputable def krylovNumberOperator
    (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal
    (fun j : Fin n => ((j.val : ℝ) : ℂ))

/-- P56.2: Krylov complexity as a finite sum. -/
noncomputable def krylovComplexity
    {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  ∑ j : Fin n,
    (j.val : ℝ) * Complex.normSq (psi j)

/-- P56.3: Krylov complexity of the evolved state. -/
noncomputable def krylovComplexityAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  krylovComplexity (jacobiState n a b t psi)

/-- P56.4: The number operator acts diagonally. -/
theorem krylovNumberOperator_mulVec
    (n : ℕ) (psi : Fin n → ℂ) :
    (krylovNumberOperator n).mulVec psi =
      fun j : Fin n => ((j.val : ℝ) : ℂ) * psi j := by
  funext j
  exact Matrix.mulVec_diagonal
    (fun k : Fin n => ((k.val : ℝ) : ℂ))
    psi j

/-- P56.5: Matrix expectation equals Krylov complexity. -/
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

/-- P56.6: Krylov complexity at time zero. -/
theorem krylovComplexityAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovComplexityAt n a b 0 psi =
      krylovComplexity psi := by
  unfold krylovComplexityAt
  rw [jacobiState_zero]

/-- P57.1: Nonnegativity of Krylov complexity. -/
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

/-- P57.2: Nonnegativity under Jacobi evolution. -/
theorem krylovComplexityAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    0 ≤ krylovComplexityAt n a b t psi := by
  unfold krylovComplexityAt
  exact krylovComplexity_nonneg
    (jacobiState n a b t psi)

/-- P58.1: Second moment of the Krylov distribution. -/
noncomputable def krylovSecondMoment
    {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  ∑ j : Fin n,
    ((j.val : ℝ) ^ 2) * Complex.normSq (psi j)

/-- P58.2: Second moment under Jacobi evolution. -/
noncomputable def krylovSecondMomentAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  krylovSecondMoment (jacobiState n a b t psi)

/-- P58.3: Nonnegativity of the second moment. -/
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

/-- P58.4: Nonnegativity of the evolved second moment. -/
theorem krylovSecondMomentAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    0 ≤ krylovSecondMomentAt n a b t psi := by
  unfold krylovSecondMomentAt
  exact krylovSecondMoment_nonneg
    (jacobiState n a b t psi)

/-- P58.5: Second moment at time zero. -/
theorem krylovSecondMomentAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovSecondMomentAt n a b 0 psi =
      krylovSecondMoment psi := by
  unfold krylovSecondMomentAt
  rw [jacobiState_zero]

/-- P59.1: Krylov variance expression. -/
noncomputable def krylovVariance
    {n : ℕ} (psi : Fin n → ℂ) : ℝ :=
  krylovSecondMoment psi -
    (krylovComplexity psi) ^ 2

/-- P59.2: Krylov variance under Jacobi evolution. -/
noncomputable def krylovVarianceAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  krylovVariance (jacobiState n a b t psi)

/-- P59.3: Variance at time zero. -/
theorem krylovVarianceAt_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    krylovVarianceAt n a b 0 psi =
      krylovVariance psi := by
  unfold krylovVarianceAt
  rw [jacobiState_zero]

/-- P59.4: Normalization is preserved by evolution. -/
theorem jacobiState_normalized
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    jacobiNormSq (jacobiState n a b t psi) = 1 := by
  rw [jacobiNormSq_state]
  exact hnorm

/-- P60.1: Centered variance identity. -/
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

/-- P60.2: Nonnegativity of normalized Krylov variance. -/
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

/-- P60.3: Nonnegativity under normalized evolution. -/
theorem krylovVarianceAt_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    0 ≤ krylovVarianceAt n a b t psi := by
  unfold krylovVarianceAt
  apply krylovVariance_nonneg
  exact jacobiState_normalized n a b t psi hnorm

/-- P61.1: Zero variance iff the centered sum is zero. -/
theorem krylovVariance_eq_zero_iff_centered
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    krylovVariance psi = 0 ↔
      (∑ j : Fin n,
        ((j.val : ℝ) - krylovComplexity psi) ^ 2 *
          Complex.normSq (psi j)) = 0 := by
  rw [krylovVariance_centered psi hnorm]

/-- P61.2: Centered variance identity at time t. -/
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

/-- P61.3: Zero variance at time t. -/
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

/-- P62.1: Every centered term vanishes at zero variance. -/
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

/-- P62.2: Zero probability away from the mean. -/
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

/-- P63.1: Every occupied level equals the Krylov mean. -/
theorem krylovVariance_zero_occupied_mean
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1)
    (hzero : krylovVariance psi = 0)
    (j : Fin n)
    (hj : Complex.normSq (psi j) ≠ 0) :
    (j.val : ℝ) = krylovComplexity psi := by
  by_contra hne
  exact hj
    (krylovVariance_zero_off_mean psi hnorm hzero j hne)

/-- P63.2: Two occupied levels must coincide. -/
theorem krylovVariance_zero_occupied_unique
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1)
    (hzero : krylovVariance psi = 0)
    (j k : Fin n)
    (hj : Complex.normSq (psi j) ≠ 0)
    (hk : Complex.normSq (psi k) ≠ 0) :
    j = k := by

  have hjmean :
      (j.val : ℝ) = krylovComplexity psi :=
    krylovVariance_zero_occupied_mean psi hnorm hzero j hj

  have hkmean :
      (k.val : ℝ) = krylovComplexity psi :=
    krylovVariance_zero_occupied_mean psi hnorm hzero k hk

  have hval : j.val = k.val := by
    exact_mod_cast hjmean.trans hkmean.symm

  exact Fin.ext hval

/-- P64.1: Normalization implies an occupied level exists. -/
theorem krylov_normalized_exists_occupied
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    ∃ j : Fin n, 0 < Complex.normSq (psi j) := by
  by_contra h
  push_neg at h
  have hall :
      ∀ j : Fin n, Complex.normSq (psi j) = 0 := by
    intro j
    exact le_antisymm (h j) (Complex.normSq_nonneg (psi j))
  have hzero : jacobiNormSq psi = 0 := by
    change (∑ j : Fin n, Complex.normSq (psi j)) = 0
    simp [hall]
  linarith

/-- P64.2: Exactly one occupied level when variance is zero. -/
theorem krylovVariance_zero_existsUnique_occupied
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1)
    (hzero : krylovVariance psi = 0) :
    ∃! j : Fin n, 0 < Complex.normSq (psi j) := by
  obtain ⟨j, hj⟩ := krylov_normalized_exists_occupied psi hnorm
  refine ⟨j, hj, ?_⟩
  intro k hk
  have hjne : Complex.normSq (psi j) ≠ 0 := ne_of_gt hj
  have hkne : Complex.normSq (psi k) ≠ 0 := ne_of_gt hk
  exact krylovVariance_zero_occupied_unique
    psi hnorm hzero k j hkne hjne

end Lanzarini
