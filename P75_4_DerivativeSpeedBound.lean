
import P75_3_QuadraticSpeedBound

namespace Lanzarini

/--
P75.4: The square of the physical derivative
of Krylov complexity is bounded by four times
the variance and the squared physical velocity.

The derivative is proved by P75.2b.
The quadratic estimate is proved by P75.3.
No desired inequality is assumed.
-/
theorem p75_derivative_speed_bound
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
          jacobiNormSq
            (((-Complex.I) • jacobiComplex n a b).mulVec
              (jacobiState n a b t psi)) := by

  let r : ℝ :=
    (jacobiInner
      (krylovCenteredState
        (jacobiState n a b t psi))
      (((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi))).re

  have hderiv :
      HasDerivAt
        (fun s : ℝ =>
          krylovComplexityAt n a b s psi)
        (2 * r) t := by
    exact p75_centered_derivative
      n a b t psi hnorm

  have hbound :
      r ^ 2 ≤
        krylovVarianceAt n a b t psi *
          jacobiNormSq
            (((-Complex.I) • jacobiComplex n a b).mulVec
              (jacobiState n a b t psi)) := by
    exact p75_physical_quadratic_bound
      n a b t psi hnorm

  refine ⟨2 * r, hderiv, ?_⟩

  nlinarith [hbound]

#print axioms p75_derivative_speed_bound

end Lanzarini
