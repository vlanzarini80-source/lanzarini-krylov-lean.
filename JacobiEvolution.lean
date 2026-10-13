
import Mathlib
import JacobiReal

namespace Lanzarini

/--
Matrice di Jacobi reale rappresentata su C.
-/
noncomputable def jacobiComplex
    (n : ℕ) (a b : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (jacobiReal n a b).map (algebraMap ℝ ℂ)

/--
Generatore -i t H.
Non è l'esponenziale della matrice.
-/
noncomputable def jacobiEvolutionGenerator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((-(t : ℂ)) * Complex.I) •
    jacobiComplex n a b

end Lanzarini
