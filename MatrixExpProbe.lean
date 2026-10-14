
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
P52: audit dei lemmi dell'esponenziale
di matrici.

I controlli seguenti non assumono
l'unitarietà del propagatore.
-/

#check Matrix.exp_conjTranspose
#check Matrix.exp_add_of_commute
#check Matrix.exp_neg
#check NormedSpace.exp_zero

/--
Conferma del risultato P51 gia'
dimostrato in JacobiEvolution.lean.
-/
theorem jacobiGenerator_skewAdjoint_check
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    (jacobiEvolutionGenerator n a b t).conjTranspose =
      -jacobiEvolutionGenerator n a b t := by
  exact jacobiEvolutionGenerator_conjTranspose n a b t

end Lanzarini
