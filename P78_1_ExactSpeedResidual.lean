
import P77_2_EnergyMeanConservation

namespace Lanzarini

/-!
P78.1: Exact residual identity for the centered-energy
Krylov speed channel. Candidate: CI verification required.

No new axioms or unproved assumptions. This does not yet
identify the centered energy variance with the initial
Jacobi coupling squared, or derive the local defect series.
-/

/-- Twice the real centered Krylov/energy-velocity pairing. -/
noncomputable def p78_speedChannelAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) : ℝ :=
  2 * (jacobiInner
    (krylovCenteredState (jacobiState n a b t psi))
    (fun j => -Complex.I *
      (p76_centeredEnergy n a b
        (jacobiState n a b t psi)) j)).re

/-- Exact Gram/imaginary-channel decomposition of the
    energy-variance speed residual. -/
theorem p78_1_exact_speed_residual
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    4 * krylovVarianceAt n a b t psi *
        p76_energyVarianceAt n a b t psi -
      (p78_speedChannelAt n a b t psi) ^ 2 =
      4 * krylovGramSum
        (krylovCenteredState (jacobiState n a b t psi))
        (fun j => -Complex.I *
          (p76_centeredEnergy n a b
            (jacobiState n a b t psi)) j) +
      4 * (jacobiInner
        (krylovCenteredState (jacobiState n a b t psi))
        (fun j => -Complex.I *
          (p76_centeredEnergy n a b
            (jacobiState n a b t psi)) j)).im ^ 2 := by
  let w : Fin n → ℂ :=
    krylovCenteredState (jacobiState n a b t psi)
  let v : Fin n → ℂ :=
    fun j => -Complex.I *
      (p76_centeredEnergy n a b
        (jacobiState n a b t psi)) j
  have hgap :=
    krylovCenteredState_gap_at n a b t psi v hnorm
  change
    krylovVarianceAt n a b t psi * jacobiNormSq v -
      (jacobiInner w v).re ^ 2 =
      krylovGramSum w v + (jacobiInner w v).im ^ 2
    at hgap
  have hv :
      jacobiNormSq v =
        p76_energyVarianceAt n a b t psi := by
    change
      jacobiNormSq (fun j => -Complex.I *
        (p76_centeredEnergy n a b
          (jacobiState n a b t psi)) j) =
        p76_energyVariance n a b
          (jacobiState n a b t psi)
    exact p76_5b_centeredVelocity_variance
      n a b (jacobiState n a b t psi)
  rw [hv] at hgap
  change
    4 * krylovVarianceAt n a b t psi *
        p76_energyVarianceAt n a b t psi -
      (2 * (jacobiInner w v).re) ^ 2 =
      4 * krylovGramSum w v +
      4 * (jacobiInner w v).im ^ 2
  nlinarith [hgap]

/-- The exact residual is nonnegative. -/
theorem p78_1_speed_residual_nonneg
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    0 ≤ 4 * krylovVarianceAt n a b t psi *
          p76_energyVarianceAt n a b t psi -
        (p78_speedChannelAt n a b t psi) ^ 2 := by
  rw [p78_1_exact_speed_residual n a b t psi hnorm]
  have hg := krylovGramSum_nonneg
    (krylovCenteredState (jacobiState n a b t psi))
    (fun j => -Complex.I *
      (p76_centeredEnergy n a b
        (jacobiState n a b t psi)) j)
  have hi := sq_nonneg
    (jacobiInner
      (krylovCenteredState (jacobiState n a b t psi))
      (fun j => -Complex.I *
        (p76_centeredEnergy n a b
          (jacobiState n a b t psi)) j)).im
  nlinarith

#print axioms p78_1_exact_speed_residual
#print axioms p78_1_speed_residual_nonneg

end Lanzarini
