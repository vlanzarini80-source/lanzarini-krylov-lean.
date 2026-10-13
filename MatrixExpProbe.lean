
import Mathlib
import JacobiEvolution

/-!
Controllo dell'API dell'esponenziale di matrice.
Nessuna dimostrazione del teorema P49 è presupposta.
-/

#check NormedSpace.exp
#check NormedSpace.exp_zero
#check Matrix.exp_conjTranspose
#check Matrix.exp_neg

namespace Lanzarini

noncomputable def jacobiPropagator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (jacobiEvolutionGenerator n a b t)

end Lanzarini
