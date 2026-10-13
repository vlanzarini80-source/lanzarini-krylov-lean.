
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
  change star ((jacobiReal n a b j i : ℝ) : ℂ) =
    ((jacobiReal n a b i j : ℝ) : ℂ)
  simpa using
    congrArg (fun x : ℝ => (x : ℂ))
      (jacobiRealEntry_symmetric a b j i)

/-
P50: controllo preliminare dei lemmi mathlib.

Questi comandi non dimostrano un nuovo teorema.
Servono a verificare quali strumenti sono
disponibili nella versione Lean/mathlib del progetto.
-/

#check Matrix.conjTranspose_apply
#check Matrix.conjTranspose_smul
#check star_smul
#check Complex.conj_I
#check star_neg

end Lanzarini
