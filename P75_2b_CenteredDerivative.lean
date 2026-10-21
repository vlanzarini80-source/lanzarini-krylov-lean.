
import P75_2a_VelocityOrthogonality

namespace Lanzarini

/-!
P75.2b: Centered physical derivative of
finite-dimensional Krylov complexity.

No sorry, admit, or new axioms.
-/

/--
Algebraic centered inner-product identity.
-/
theorem p75_centered_inner_identity
    {n : ℕ}
    (u v : Fin n → ℂ) :
    jacobiInner (krylovCenteredState u) v =
      (∑ j : Fin n,
        (j.val : ℂ) * (star (u j) * v j)) -
      (krylovComplexity u : ℂ) *
        jacobiInner u v := by

  unfold jacobiInner krylovCenteredState

  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]

  apply Finset.sum_congr rfl
  intro j hj

  push_cast
  simp only [star_mul', star_ofReal]
  ring

/--
Physical centered derivative of Krylov complexity.
-/
theorem p75_centered_derivative
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexityAt n a b s psi)
      (2 *
        (jacobiInner
          (krylovCenteredState
            (jacobiState n a b t psi))
          (((-Complex.I) • jacobiComplex n a b).mulVec
            (jacobiState n a b t psi))).re)
      t := by

  let u : Fin n → ℂ :=
    jacobiState n a b t psi

  let v : Fin n → ℂ :=
    ((-Complex.I) • jacobiComplex n a b).mulVec u

  have horth :
      (jacobiInner u v).re = 0 := by
    exact p75_state_velocity_real_orthogonal
      n a b t psi

  have hinner :=
    p75_centered_inner_identity u v

  have hreal :
      (jacobiInner (krylovCenteredState u) v).re =
        ∑ j : Fin n,
          (j.val : ℝ) *
            (star (u j) * v j).re := by

    have h := congrArg Complex.re hinner

    simp only [
      Complex.sub_re,
      Complex.mul_re,
      Complex.ofReal_re,
      Complex.ofReal_im,
      mul_zero,
      sub_zero,
      map_sum
    ] at h

    rw [horth] at h
    simp only [mul_zero, sub_zero] at h

    convert h using 1
    apply Finset.sum_congr rfl
    intro j hj
    simp

  have hbase :=
    p74_krylovComplexityAt_hasDerivAt
      n a b t psi

  change
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexityAt n a b s psi)
      (2 *
        (jacobiInner (krylovCenteredState u) v).re)
      t

  rw [hreal]
  exact hbase

#print axioms p75_centered_inner_identity
#print axioms p75_centered_derivative

end Lanzarini
