
import Mathlib
import JacobiEvolution

namespace Lanzarini

/--
Propagatore quantistico associato alla
matrice di Jacobi reale H:

U(t) = exp(-i t H).
-/
noncomputable def jacobiPropagator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ℂ
    (jacobiEvolutionGenerator n a b t)

/--
Al tempo zero il generatore è nullo.
-/
theorem jacobiEvolutionGenerator_zero
    (n : ℕ) (a b : Fin n → ℝ) :
    jacobiEvolutionGenerator n a b 0 = 0 := by
  simp [jacobiEvolutionGenerator]

/--
Il propagatore al tempo zero
è la matrice identità.
-/
theorem jacobiPropagator_zero
    (n : ℕ) (a b : Fin n → ℝ) :
    jacobiPropagator n a b 0 = 1 := by
  rw [jacobiPropagator]
  rw [jacobiEvolutionGenerator_zero]
  exact NormedSpace.exp_zero

/-
P52: audit delle firme effettive dei
lemmi per l'esponenziale matriciale.
-/

#print Matrix.exp_conjTranspose
#print Matrix.exp_add_of_commute
#print Matrix.exp_neg

/--
Conferma del risultato P51.
-/
theorem jacobiGenerator_skewAdjoint_check
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    (jacobiEvolutionGenerator n a b t).conjTranspose =
      -jacobiEvolutionGenerator n a b t := by
  exact jacobiEvolutionGenerator_conjTranspose n a b t

end Lanzarini
