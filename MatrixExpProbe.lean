
import Mathlib
import JacobiEvolution

/-!
Verifica dell'esponenziale di matrice
in mathlib 4.24.0.
-/

#check NormedSpace.exp
#check NormedSpace.exp_zero
#check Matrix.exp_conjTranspose
#check Matrix.exp_neg

namespace Lanzarini

/--
Propagatore quantistico:
U(t) = exp(-i t H).
-/
noncomputable def jacobiPropagator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ℂ
    (jacobiEvolutionGenerator n a b t)

end Lanzarini
 
