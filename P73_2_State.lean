
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

  -- Applying a matrix to a fixed vector is real-linear.
  let applyVec :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ]
        (Fin n → ℂ) :=
    (LinearMap.applyₗ (R := ℝ) psi).comp
      (Matrix.mulVecBilin ℝ ℝ)

  -- Finite-dimensional linear maps are continuous.
  let applyVecC :
      Matrix (Fin n) (Fin n) ℂ →L[ℝ]
        (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap applyVec

  -- Use the verified propagator derivative P73.1.
  have hU :=
    p73_jacobiPropagator_hasDerivAt n a b t

  -- Apply a continuous linear map to the derivative.
  have hcomp :=
    applyVecC.hasFDerivAt.comp_hasDerivAt t hU

  have hstate :
      HasDerivAt
        (fun s : ℝ =>
          (jacobiPropagator n a b s).mulVec psi)
        ((((-Complex.I) • jacobiComplex n a b) *
          jacobiPropagator n a b t).mulVec psi)
        t := by
    exact hcomp

  -- Correct direction of matrix-vector associativity.
  rw [← Matrix.mulVec_mulVec] at hstate

  -- Recover the original definition of jacobiState.
  exact hstate

end Lanzarini

#print axioms Lanzarini.p73_jacobiState_hasDerivAt
