
import KrylovLagrange

/-!
LANZARINI-KRYLOV-LEAN
P70: Exact Gram and scalar-channel decomposition.
P71: Centered Krylov state and variance bridge.

The statements of P70.1 and P70.2 are unchanged.
No theorem assumes a speed-limit inequality or a time derivative.
-/

namespace Lanzarini

/-- P70.1: Exact real-part gap identity. -/
theorem krylovGram_realPart_gap
    {n : ℕ} (u v : Fin n → ℂ) :
    (∑ i : Fin n, Complex.normSq (u i)) *
      (∑ i : Fin n, Complex.normSq (v i)) -
      ((∑ i : Fin n, star (u i) * v i).re) ^ 2 =
    krylovGramSum u v +
      ((∑ i : Fin n, star (u i) * v i).im) ^ 2 := by
  have h := krylovLagrange_finite u v
  rw [Complex.normSq_apply] at h
  nlinarith

/-- P70.2: Nonnegativity of the real-part gap. -/
theorem krylovGram_realPart_gap_nonneg
    {n : ℕ} (u v : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, Complex.normSq (u i)) *
       (∑ i : Fin n, Complex.normSq (v i)) -
       ((∑ i : Fin n, star (u i) * v i).re) ^ 2 := by
  rw [krylovGram_realPart_gap]
  exact add_nonneg
    (krylovGramSum_nonneg u v)
    (sq_nonneg _)

/-- P71.1: The centered Krylov state (N - K) psi. -/
noncomputable def krylovCenteredState
    {n : ℕ} (psi : Fin n → ℂ) : Fin n → ℂ :=
  fun j =>
    (((j.val : ℝ) - krylovComplexity psi : ℝ) : ℂ) * psi j

/-- P71.2: For a normalized state, the squared norm of
    the centered state equals the Krylov variance. -/
theorem krylovCenteredState_normSq
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    jacobiNormSq (krylovCenteredState psi) =
      krylovVariance psi := by
  calc
    jacobiNormSq (krylovCenteredState psi) =
        ∑ j : Fin n,
          ((j.val : ℝ) - krylovComplexity psi) ^ 2 *
            Complex.normSq (psi j) := by
              unfold jacobiNormSq krylovCenteredState
              apply Finset.sum_congr rfl
              intro j _
              rw [Complex.normSq_mul, Complex.normSq_ofReal]
              ring
    _ = krylovVariance psi :=
      (krylovVariance_centered psi hnorm).symm

/-- P71.3: The same identity holds at every real time
    for normalized Jacobi evolution. -/
theorem krylovCenteredState_normSq_at
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    jacobiNormSq (krylovCenteredState
      (jacobiState n a b t psi)) =
    krylovVarianceAt n a b t psi := by
  unfold krylovVarianceAt
  exact krylovCenteredState_normSq
    (jacobiState n a b t psi)
    (jacobiState_normalized n a b t psi hnorm)

/-- P71.4: The P70 gap identity applied to the
    centered time-evolved Krylov state and any velocity candidate v.
    No Schrödinger derivative is asserted here. -/
theorem krylovCenteredState_gap_at
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi v : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    krylovVarianceAt n a b t psi * jacobiNormSq v -
      (jacobiInner
        (krylovCenteredState (jacobiState n a b t psi)) v).re ^ 2 =
    krylovGramSum
      (krylovCenteredState (jacobiState n a b t psi)) v +
      (jacobiInner
        (krylovCenteredState (jacobiState n a b t psi)) v).im ^ 2 := by
  have h := krylovGram_realPart_gap
    (krylovCenteredState (jacobiState n a b t psi)) v
  change
    jacobiNormSq (krylovCenteredState (jacobiState n a b t psi)) *
      jacobiNormSq v -
      (jacobiInner
        (krylovCenteredState (jacobiState n a b t psi)) v).re ^ 2 =
      krylovGramSum
        (krylovCenteredState (jacobiState n a b t psi)) v +
      (jacobiInner
        (krylovCenteredState (jacobiState n a b t psi)) v).im ^ 2 at h
  rw [krylovCenteredState_normSq_at n a b t psi hnorm] at h
  exact h

end Lanzarini
