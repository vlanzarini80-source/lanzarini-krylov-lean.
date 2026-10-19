
import P73_RealTime
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-
P73.2: Real-time derivative of the evolved Jacobi state.

The result is derived from P73.1.

No state differentiability assumption is introduced.
No Schrodinger equation is assumed.
No normalization hypothesis is required.
-/

open scoped Matrix.Norms.Operator

namespace Lanzarini

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p73_jacobiState_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    HasDerivAt
      (fun s : ℝ => jacobiState n a b s psi)
      (((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi))
      t := by

  -- Matrix action on a fixed initial state is real-linear.
  let applyVec :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ]
        (Fin n → ℂ) :=
    (LinearMap.applyₗ (R := ℝ) psi).comp
      (Matrix.mulVecBilin ℝ ℝ)

  -- A linear map on this finite-dimensional
  -- normed space is continuous.
  let applyVecC :
      Matrix (Fin n) (Fin n) ℂ →L[ℝ]
        (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap applyVec

  -- P73.1: derivative of the propagator.
  have hU :=
    p73_jacobiPropagator_hasDerivAt n a b t

  -- Apply the continuous linear map.
  have hcomp :=
    applyVecC.hasFDerivAt.comp_hasDerivAt t hU

  -- Express the result as matrix-vector multiplication.
  have hstate :
      HasDerivAt
        (fun s : ℝ =>
          (jacobiPropagator n a b s).mulVec psi)
        ((((-Complex.I) • jacobiComplex n a b) *
          jacobiPropagator n a b t).mulVec psi)
        t := by
    exact hcomp

  -- Use associativity of matrix-vector multiplication.
  rw [Matrix.mulVec_mulVec] at hstate

  -- Recover the original definition of jacobiState.
  exact hstate

end Lanzarini

#print axioms Lanzarini.p73_jacobiState_hasDerivAt
