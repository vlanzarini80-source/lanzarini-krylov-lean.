
import P76_5b_CenteredVelocityNorm

namespace Lanzarini

/-!
P76.6: Energy-variance speed limit for
finite-dimensional Jacobi evolution.

No new axioms.
No sorry or admit.
The target inequality is not an assumption.

Candidate requiring actual Lean CI verification.
-/

/--
The physical velocity written using the
scaled Hamiltonian equals pointwise
multiplication of Hu by -i.
-/
private theorem p76_6_velocity_bridge
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
The physical derivative of Krylov complexity
is bounded by the product of Krylov variance
and centered energy variance.

The derivative and the bound are both
derived from previously established results.
-/
theorem p76_6_energy_speed_limit
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
      d ^ 2 ≤
        4 * krylovVarianceAt n a b t psi *
          p76_energyVarianceAt n a b t psi := by

  let u : Fin n → ℂ :=
    jacobiState n a b t psi

  let v : Fin n → ℂ :=
    fun j =>
      -Complex.I *
        (p76_centeredEnergy n a b u) j

  let r : ℝ :=
    (jacobiInner (krylovCenteredState u) v).re

  have hbridge :
      (((-Complex.I) • jacobiComplex n a b).mulVec u) =
        (fun j =>
          -Complex.I *
            ((jacobiComplex n a b).mulVec u) j) :=
    p76_6_velocity_bridge n a b u

  have hinner :
      jacobiInner (krylovCenteredState u) v =
        jacobiInner
          (krylovCenteredState u)
          (((-Complex.I) • jacobiComplex n a b).mulVec u) := by
    unfold v
    rw [hbridge]
    exact p76_5_centered_velocity_inner
      n a b u
      (jacobiNormSq_state n a b t psi ▸ hnorm)

  have hderiv :
      HasDerivAt
        (fun s : ℝ =>
          krylovComplexityAt n a b s psi)
        (2 * r) t := by
    have h :=
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
        t at h
    rw [← hinner] at h
    exact h

  have hbound :
      r ^ 2 ≤
        krylovVarianceAt n a b t psi *
          jacobiNormSq v := by
    exact p75_centered_quadratic_bound
      n a b t psi v hnorm

  have hvariance :
      jacobiNormSq v =
        p76_energyVarianceAt n a b t psi := by
    unfold v p76_energyVarianceAt
    exact p76_5b_centeredVelocity_variance
      n a b u

  refine ⟨2 * r, hderiv, ?_⟩
  rw [hvariance] at hbound
  nlinarith [hbound]

#print axioms p76_6_energy_speed_limit

end Lanzarini
