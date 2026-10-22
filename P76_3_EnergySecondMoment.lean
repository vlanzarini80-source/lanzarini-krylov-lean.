
import P76_2_EnergyVarianceIdentity

namespace Lanzarini

/-!
P76.3: Energy variance as a second moment.

The Jacobi Hamiltonian is Hermitian by the
previously established theorem
`jacobiComplex_conjTranspose`.

No new axioms and no assumed variance identity.

The proof must be checked by Lean CI.
-/

/--
Hermiticity gives
  <Hu, Hu> = <u, H(Hu)>.
-/
private theorem p76_inner_energy_second_moment
    (n : ℕ) (a b : Fin n → ℝ)
    (u : Fin n → ℂ) :
    jacobiInner
        ((jacobiComplex n a b).mulVec u)
        ((jacobiComplex n a b).mulVec u) =
      jacobiInner u
        ((jacobiComplex n a b).mulVec
          ((jacobiComplex n a b).mulVec u)) := by
  unfold jacobiInner
  let H := jacobiComplex n a b
  change
    dotProduct (star (H.mulVec u)) (H.mulVec u) =
      dotProduct (star u) (H.mulVec (H.mulVec u))
  rw [Matrix.star_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul]
  have hH : H.conjTranspose = H := by
    exact jacobiComplex_conjTranspose n a b
  rw [hH]
  rw [Matrix.dotProduct_mulVec]
  exact (Matrix.vecMul_vecMul (star u) H H).symm

/--
The squared norm of Hu is the real part
of the energy second moment.
-/
theorem p76_energyNormSq_secondMoment
    (n : ℕ) (a b : Fin n → ℝ)
    (u : Fin n → ℂ) :
    jacobiNormSq
        ((jacobiComplex n a b).mulVec u) =
      (jacobiInner u
        ((jacobiComplex n a b).mulVec
          ((jacobiComplex n a b).mulVec u))).re := by
  have h :=
    p76_inner_energy_second_moment n a b u
  rw [jacobiInner_self] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re] using hre

/--
For a normalized state, energy variance equals
the real second moment minus squared mean.
-/
theorem p76_energyVariance_secondMoment
    (n : ℕ) (a b : Fin n → ℝ)
    (u : Fin n → ℂ)
    (hnorm : jacobiNormSq u = 1) :
    p76_energyVariance n a b u =
      (jacobiInner u
        ((jacobiComplex n a b).mulVec
          ((jacobiComplex n a b).mulVec u))).re -
        (p76_energyMean n a b u) ^ 2 := by
  rw [p76_energyVariance_identity n a b u hnorm]
  rw [p76_energyNormSq_secondMoment]

/--
The same second-moment identity along
unitary Jacobi evolution.
-/
theorem p76_energyVarianceAt_secondMoment
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    p76_energyVarianceAt n a b t psi =
      (jacobiInner
        (jacobiState n a b t psi)
        ((jacobiComplex n a b).mulVec
          ((jacobiComplex n a b).mulVec
            (jacobiState n a b t psi)))).re -
        (p76_energyMean n a b
          (jacobiState n a b t psi)) ^ 2 := by
  unfold p76_energyVarianceAt
  apply p76_energyVariance_secondMoment
  rw [jacobiNormSq_state]
  exact hnorm

#print axioms p76_energyNormSq_secondMoment
#print axioms p76_energyVariance_secondMoment
#print axioms p76_energyVarianceAt_secondMoment

end Lanzarini
