
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
Generatore -i t H dell'evoluzione quantistica.
-/
noncomputable def jacobiEvolutionGenerator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((-(t : ℂ)) * Complex.I) •
    jacobiComplex n a b

/--
La matrice di Jacobi complessa è autoaggiunta:
H† = H.
-/
theorem jacobiComplex_conjTranspose
    (n : ℕ) (a b : Fin n → ℝ) :
    (jacobiComplex n a b).conjTranspose =
      jacobiComplex n a b := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  change star ((algebraMap ℝ ℂ)
    (jacobiReal n a b j i)) =
    (algebraMap ℝ ℂ) (jacobiReal n a b i j)
  simp only [Complex.star_def]
  norm_cast
  exact jacobiRealEntry_symmetric a b j i


end Lanzarini
