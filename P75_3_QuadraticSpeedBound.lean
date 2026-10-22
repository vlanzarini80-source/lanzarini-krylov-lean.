
import P75_2b_CenteredDerivative

namespace Lanzarini

/--
P75.3: Quadratic bound for the centered
Krylov derivative channel.

The result follows from the exact Gram-gap
identity and positivity of its two terms.
-/
theorem p75_centered_quadratic_bound
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi v : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    (jacobiInner
      (krylovCenteredState
        (jacobiState n a b t psi))
      v).re ^ 2
      ≤
    krylovVarianceAt n a b t psi *
      jacobiNormSq v := by

  let w : Fin n → ℂ :=
    krylovCenteredState
      (jacobiState n a b t psi)

  have hgap :=
    krylovCenteredState_gap_at
      n a b t psi v hnorm

  have hgram :
      0 ≤ krylovGramSum w v :=
    krylovGramSum_nonneg w v

  have himag :
      0 ≤ (jacobiInner w v).im ^ 2 :=
    sq_nonneg _

  change
    krylovVarianceAt n a b t psi *
        jacobiNormSq v -
      (jacobiInner w v).re ^ 2 =
        krylovGramSum w v +
        (jacobiInner w v).im ^ 2
    at hgap

  change
    (jacobiInner w v).re ^ 2 ≤
      krylovVarianceAt n a b t psi *
        jacobiNormSq v

  nlinarith

/--
P75.3: Physical velocity specialization.
-/
theorem p75_physical_quadratic_bound
    (n : ℕ)
    (a b : Fin n → ℝ)
    (t : ℝ)
    (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    (jacobiInner
      (krylovCenteredState
        (jacobiState n a b t psi))
      (((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi))).re ^ 2
      ≤
    krylovVarianceAt n a b t psi *
      jacobiNormSq
        (((-Complex.I) • jacobiComplex n a b).mulVec
          (jacobiState n a b t psi)) := by

  exact p75_centered_quadratic_bound
    n a b t psi
    (((-Complex.I) • jacobiComplex n a b).mulVec
      (jacobiState n a b t psi))
    hnorm

#print axioms p75_centered_quadratic_bound
#print axioms p75_physical_quadratic_bound

end Lanzarini
