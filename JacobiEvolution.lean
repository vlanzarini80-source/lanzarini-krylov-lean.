
import Mathlib
import JacobiReal

namespace Lanzarini

noncomputable def jacobiEvolution
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.exp
    ((-t * Complex.I) •
      (jacobiReal n a b).map
        (algebraMap ℝ ℂ))

end Lanzarini
