
import P78_1_ExactSpeedResidual

namespace Lanzarini

/-!
P78.2: Physical derivative and exact residual.

Connect the centered speed channel from P78.1
to the actual derivative of Krylov complexity.

No new axioms.
No assumed speed-limit inequality.
-/

private theorem p78_2_velocity_bridge
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ) :
    (((-Complex.I) • jacobiComplex n a b).mulVec u) =
      (fun j =>
        -Complex.I *
          ((jacobiComplex n a b).mulVec u) j) := by
  funext j
  simp [Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

/--
The centered speed channel is the actual
derivative of Krylov complexity.
-/
theorem p78_2_speedChannel_derivative
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexityAt n a b s psi)
      (p78_speedChannelAt n a b t psi)
      t := by

  let u : Fin n → ℂ :=
    jacobiState n a b t psi

  have hu : jacobiNormSq u = 1 := by
    dsimp [u]
    exact jacobiState_normalized
      n a b t psi hnorm

  have hinner :
      jacobiInner
        (krylovCenteredState u)
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy n a b u) j) =
      jacobiInner
        (krylovCenteredState u)
        (((-Complex.I) • jacobiComplex n a b).mulVec u) := by
    rw [p78_2_velocity_bridge n a b u]
    exact p76_5_centered_velocity_inner
      n a b u hu

  have hderiv :=
    p75_centered_derivative
      n a b t psi hnorm

  change
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexityAt n a b s psi)
      (2 *
        (jacobiInner
          (krylovCenteredState u)
          (((-Complex.I) • jacobiComplex n a b).mulVec u)).re)
      t at hderiv

  rw [← hinner] at hderiv

  change
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexityAt n a b s psi)
      (p78_speedChannelAt n a b t psi)
      t at hderiv

  exact hderiv

/--
Exact Gram decomposition for the actual
physical derivative, with nonnegative residual.
-/
theorem p78_2_exact_physical_residual
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    ∃ d : ℝ,
      HasDerivAt
        (fun s : ℝ =>
          krylovComplexityAt n a b s psi)
        d t
      ∧
      4 * krylovVarianceAt n a b t psi *
          p76_energyVarianceAt n a b t psi -
        d ^ 2 =
        4 * krylovGramSum
          (krylovCenteredState
            (jacobiState n a b t psi))
          (fun j =>
            -Complex.I *
              (p76_centeredEnergy n a b
                (jacobiState n a b t psi)) j) +
        4 * (jacobiInner
          (krylovCenteredState
            (jacobiState n a b t psi))
          (fun j =>
            -Complex.I *
              (p76_centeredEnergy n a b
                (jacobiState n a b t psi)) j)).im ^ 2
      ∧
      0 ≤
        4 * krylovVarianceAt n a b t psi *
          p76_energyVarianceAt n a b t psi -
        d ^ 2 := by

  refine
    ⟨p78_speedChannelAt n a b t psi,
      p78_2_speedChannel_derivative
        n a b t psi hnorm,
      p78_1_exact_speed_residual
        n a b t psi hnorm,
      p78_1_speed_residual_nonneg
        n a b t psi hnorm⟩

#print axioms p78_2_speedChannel_derivative
#print axioms p78_2_exact_physical_residual

end Lanzarini
