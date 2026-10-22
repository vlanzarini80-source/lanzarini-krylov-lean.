
import P76_1_EnergyVariance

namespace Lanzarini

/-!
P76.2: expansion of the centered energy norm.
Candidate proof; requires actual Lean 4 / mathlib CI verification.
No additional axioms or assumptions of the desired identity.
-/

private theorem p76_normSq_centered_term
    (z w : ℂ) (m : ℝ) :
    Complex.normSq (w - (m : ℂ) * z) =
      Complex.normSq w -
        2 * m * (star z * w).re +
        m ^ 2 * Complex.normSq z := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

private theorem p76_normSq_centered_expansion
    {n : ℕ} (u w : Fin n → ℂ) (m : ℝ) :
    jacobiNormSq (fun j => w j - (m : ℂ) * u j) =
      jacobiNormSq w -
        2 * m * (jacobiInner u w).re +
        m ^ 2 * jacobiNormSq u := by
  unfold jacobiNormSq jacobiInner
  simp_rw [p76_normSq_centered_term]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [← Complex.re_sum]

/-- The usual energy-variance identity for a normalized finite state. -/
theorem p76_energyVariance_identity
    (n : ℕ) (a b : Fin n → ℝ)
    (u : Fin n → ℂ)
    (hnorm : jacobiNormSq u = 1) :
    p76_energyVariance n a b u =
      jacobiNormSq ((jacobiComplex n a b).mulVec u) -
        (p76_energyMean n a b u) ^ 2 := by
  unfold p76_energyVariance p76_centeredEnergy
  rw [p76_normSq_centered_expansion]
  change
    jacobiNormSq ((jacobiComplex n a b).mulVec u) -
      2 * p76_energyMean n a b u *
        (jacobiInner u ((jacobiComplex n a b).mulVec u)).re +
      (p76_energyMean n a b u) ^ 2 * jacobiNormSq u =
    jacobiNormSq ((jacobiComplex n a b).mulVec u) -
      (p76_energyMean n a b u) ^ 2
  rw [hnorm]
  unfold p76_energyMean
  ring

/-- The same identity along the actual Jacobi evolution. -/
theorem p76_energyVarianceAt_identity
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    p76_energyVarianceAt n a b t psi =
      jacobiNormSq
        ((jacobiComplex n a b).mulVec (jacobiState n a b t psi)) -
      (p76_energyMean n a b (jacobiState n a b t psi)) ^ 2 := by
  unfold p76_energyVarianceAt
  apply p76_energyVariance_identity
  rw [jacobiNormSq_state]
  exact hnorm

#print axioms p76_energyVariance_identity
#print axioms p76_energyVarianceAt_identity

end Lanzarini
