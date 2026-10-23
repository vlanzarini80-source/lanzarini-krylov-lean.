
import P76_5_CenteredVelocity

namespace Lanzarini

/-!
P76.5b: Norm of the centered physical velocity.

No new axioms.
No sorry or admit.
No assumption of the desired speed inequality.

Requires actual Lean CI verification.
-/

/--
Multiplication by -i preserves the squared
complex norm.
-/
private theorem p76_5b_normSq_negI
    (z : ℂ) :
    Complex.normSq (-Complex.I * z) =
      Complex.normSq z := by
  rw [Complex.normSq_mul]
  norm_num

/--
Multiplication of a finite complex vector by -i
preserves its squared Jacobi norm.
-/
theorem p76_5b_jacobiNormSq_negI
    {n : ℕ}
    (v : Fin n → ℂ) :
    jacobiNormSq (fun j => -Complex.I * v j) =
      jacobiNormSq v := by
  unfold jacobiNormSq
  apply Finset.sum_congr rfl
  intro j hj
  exact p76_5b_normSq_negI (v j)

/--
The squared norm of the centered physical
velocity equals the energy variance.
-/
theorem p76_5b_centeredVelocity_variance
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ) :
    jacobiNormSq
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy n a b u) j) =
      p76_energyVariance n a b u := by
  rw [p76_5b_jacobiNormSq_negI]
  rfl

#print axioms p76_5b_jacobiNormSq_negI
#print axioms p76_5b_centeredVelocity_variance

end Lanzarini
