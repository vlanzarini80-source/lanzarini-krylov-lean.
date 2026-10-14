
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

/--
P51: il generatore dell'evoluzione quantistica
associato a una matrice di Jacobi reale
è anti-autoaggiunto.
-/
theorem jacobiEvolutionGenerator_conjTranspose
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    (jacobiEvolutionGenerator n a b t).conjTranspose =
      -jacobiEvolutionGenerator n a b t := by
  unfold jacobiEvolutionGenerator
  rw [Matrix.conjTranspose_smul]
  rw [jacobiComplex_conjTranspose]
  have hs :
      star ((-(t : ℂ)) * Complex.I) =
        -((-(t : ℂ)) * Complex.I) := by
    simp [star_mul, Complex.conj_I, mul_comm]
  rw [hs]
  exact neg_smul _ _

end Lanzarini
