
import KrylovGap
import Mathlib.Analysis.Complex.RealDeriv

/-
P73.1: Real-time derivative of the Jacobi propagator.
Derived from the complex-time derivative P72.3a.3.
No Schrodinger equation is assumed.
-/

open scoped Matrix.Norms.Operator

namespace Lanzarini

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p73_jacobiPropagator_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => jacobiPropagator n a b s)
      (((-Complex.I) • jacobiComplex n a b) *
        jacobiPropagator n a b t)
      t := by
  let A : Matrix (Fin n) (Fin n) ℂ :=
    (-Complex.I) • jacobiComplex n a b

  have hc :
      HasDerivAt
        (fun z : ℂ => NormedSpace.exp ℂ (z • A))
        (A * NormedSpace.exp ℂ ((t : ℂ) • A))
        (t : ℂ) := by
    dsimp [A]
    exact jacobiComplexTimeExp_hasDerivAt n a b (t : ℂ)

  have hreal :
      HasDerivAt
        (fun s : ℝ => NormedSpace.exp ℂ ((s : ℂ) • A))
        (A * NormedSpace.exp ℂ ((t : ℂ) • A))
        t := by
    have hfre := hc.hasFDerivAt.restrictScalars ℝ
    have hcomp := hfre.comp t Complex.ofRealCLM.hasFDerivAt
    simpa [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.restrictScalars_apply,
      ContinuousLinearMap.smulRight_apply,
      Complex.ofRealCLM_apply] using hcomp.hasDerivAt

  simpa only [jacobiPropagator_complex_time_eq, A] using hreal

end Lanzarini

#print axioms Lanzarini.p73_jacobiPropagator_hasDerivAt
