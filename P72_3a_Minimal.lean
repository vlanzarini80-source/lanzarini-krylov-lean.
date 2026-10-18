
import JacobiEvolution
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
P72.3a: isolated derivative test with mathlib v4.24.0.
Existing theorems in KrylovGap.lean remain unchanged.
-/

open scoped Matrix.Norms.Operator

namespace Lanzarini

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p72_matrixExp_generic_hasDerivAt
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => NormedSpace.exp ℂ (w • A))
      (A * NormedSpace.exp ℂ (z • A))
      z := by
  exact hasDerivAt_exp_smul_const' A z

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem p72_jacobiComplexTimeExp_hasDerivAt_test
    (n : ℕ) (a b : Fin n → ℝ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        NormedSpace.exp ℂ
          (w • ((-Complex.I) • jacobiComplex n a b)))
      (((-Complex.I) • jacobiComplex n a b) *
        NormedSpace.exp ℂ
          (z • ((-Complex.I) • jacobiComplex n a b)))
      z := by
  exact p72_matrixExp_generic_hasDerivAt
    n ((-Complex.I) • jacobiComplex n a b) z

end Lanzarini

#print axioms Lanzarini.p72_matrixExp_generic_hasDerivAt
#print axioms Lanzarini.p72_jacobiComplexTimeExp_hasDerivAt_test
