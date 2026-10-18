
import KrylovLagrange

/-!
LANZARINI-KRYLOV-LEAN

P70: Exact Gram and scalar-channel decomposition.
P71: Centered Krylov state and variance bridge.
P72.1: Exact Krylov complexity increment.
P72.2: Derivative for a componentwise differentiable curve.
P72.3a: Jacobi generator and complex-time matrix
        exponential derivative.

All previous theorem statements are preserved.
The real-time Schrodinger equation is not yet proved.
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

/-- P71.2: The squared norm of the centered state. -/
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

/-- P71.3: The centered norm along Jacobi evolution. -/
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

/-- P71.4: Gram gap for the centered evolved state. -/
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

/--
P72.1: Exact increment of Krylov complexity.

No normalization, differentiability, or Jacobi
evolution assumptions are required.
-/
theorem krylovComplexity_increment
    {n : ℕ} (psi h : Fin n → ℂ) :
    krylovComplexity (fun j => psi j + h j) =
      krylovComplexity psi +
      krylovComplexity h +
      2 * (∑ j : Fin n,
        (j.val : ℝ) *
          (star (psi j) * h j).re) := by
  unfold krylovComplexity
  calc
    (∑ j : Fin n,
      (j.val : ℝ) *
        Complex.normSq (psi j + h j)) =
      ∑ j : Fin n,
        ((j.val : ℝ) *
            Complex.normSq (psi j) +
         (j.val : ℝ) *
            Complex.normSq (h j) +
         2 * ((j.val : ℝ) *
            (star (psi j) * h j).re)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [
        Complex.normSq_apply,
        Complex.add_re,
        Complex.add_im,
        Complex.star_def,
        Complex.mul_re,
        Complex.conj_re,
        Complex.conj_im
      ]
      ring
    _ = _ := by
      simp only [
        Finset.sum_add_distrib,
        Finset.mul_sum
      ]

/--
P72.2: Derivative of Krylov complexity for a
componentwise differentiable curve.

The real and imaginary derivatives of each
coordinate are explicitly assumed.

No normalization or Schrodinger dynamics is
assumed, and the conclusion does not appear
among the hypotheses.
-/
theorem krylovComplexity_hasDerivAt_components
    {n : ℕ}
    (psi : ℝ → Fin n → ℂ)
    (velocity : Fin n → ℂ)
    (t : ℝ)
    (hre : ∀ j : Fin n,
      HasDerivAt
        (fun s : ℝ => (psi s j).re)
        (velocity j).re t)
    (him : ∀ j : Fin n,
      HasDerivAt
        (fun s : ℝ => (psi s j).im)
        (velocity j).im t) :
    HasDerivAt
      (fun s : ℝ => krylovComplexity (psi s))
      (2 * (∑ j : Fin n,
        (j.val : ℝ) *
          (star (psi t j) * velocity j).re))
      t := by

  have hterm (j : Fin n) :
      HasDerivAt
        (fun s : ℝ =>
          (j.val : ℝ) * Complex.normSq (psi s j))
        ((j.val : ℝ) *
          (2 * (star (psi t j) * velocity j).re))
        t := by

    have hr := (hre j).pow 2
    have hi := (him j).pow 2
    have hs := (hr.add hi).const_mul (j.val : ℝ)

    convert hs using 1
    · funext s
      simp only [
        Complex.normSq_apply,
        Pi.add_apply,
        Pi.pow_apply
      ]
      ring
    · simp only [
        Complex.star_def,
        Complex.mul_re,
        Complex.conj_re,
        Complex.conj_im,
        Nat.cast_ofNat,
        Nat.reduceSub,
        pow_one
      ]
      ring

  have hsum :=
    HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (Fin n)))
      (fun j _ => hterm j)

  have hderiv :
      (∑ j : Fin n,
        (j.val : ℝ) *
          (2 * (star (psi t j) * velocity j).re)) =
      2 * (∑ j : Fin n,
        (j.val : ℝ) *
          (star (psi t j) * velocity j).re) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

  rw [hderiv] at hsum
  exact hsum

/--
P72.3a.1: The existing Jacobi evolution
generator is t times the constant matrix -iH.
-/
theorem jacobiEvolutionGenerator_time_factor
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    jacobiEvolutionGenerator n a b t =
      (t : ℂ) •
        ((-Complex.I) • jacobiComplex n a b) := by
  unfold jacobiEvolutionGenerator
  rw [smul_smul]
  have h :
      (-(t : ℂ)) * Complex.I =
        (t : ℂ) * (-Complex.I) := by
    ring
  rw [h]

/--
P72.3a.2: The existing Jacobi propagator
equals the restriction of the complex-time
matrix exponential to real time.
-/
theorem jacobiPropagator_complex_time_eq
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    jacobiPropagator n a b t =
      NormedSpace.exp ℂ
        ((t : ℂ) •
          ((-Complex.I) • jacobiComplex n a b)) := by
  unfold jacobiPropagator
  rw [jacobiEvolutionGenerator_time_factor]

open scoped Matrix.Norms.Operator

/-
P72.3a.3: Complex-time derivative
of the original Jacobi matrix exponential.

Let A = -iH.

Then d/dz exp(z A) = A * exp(z A).

The operator norm is selected explicitly.
No real-time state derivative is asserted here.
-/
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem jacobiComplexTimeExp_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        NormedSpace.exp ℂ
          (w • ((-Complex.I) • jacobiComplex n a b)))
      (((-Complex.I) • jacobiComplex n a b) *
        NormedSpace.exp ℂ
          (z • ((-Complex.I) • jacobiComplex n a b)))
      z := by
  exact hasDerivAt_exp_smul_const'
    ((-Complex.I) • jacobiComplex n a b) z

end Lanzarini

#print axioms Lanzarini.krylovComplexity_increment
#print axioms Lanzarini.krylovComplexity_hasDerivAt_components
#print axioms Lanzarini.jacobiEvolutionGenerator_time_factor
#print axioms Lanzarini.jacobiPropagator_complex_time_eq
#print axioms Lanzarini.jacobiComplexTimeExp_hasDerivAt
