
import Mathlib
import JacobiReal

namespace Lanzarini

/--
Matrice di Jacobi reale rappresentata su C.
Questa definizione non contiene alcuna ipotesi
sugli autovalori o sui coefficienti.
-/
def jacobiComplex
    (n : ℕ) (a b : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (jacobiReal n a b).map (algebraMap ℝ ℂ)

/--
Generatore formale -i t H dell'evoluzione
quantistica per una matrice di Jacobi H.

Non è ancora l'esponenziale di matrice.
-/
def jacobiEvolutionGenerator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((-(t : ℂ)) * Complex.I) •
    jacobiComplex n a b

end Lanzarini
 
