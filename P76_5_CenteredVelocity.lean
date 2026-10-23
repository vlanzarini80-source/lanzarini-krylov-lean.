
import P76_4_CenteredEnergySpeed

namespace Lanzarini

/-!
P76.5a: Centered energy inner-product identity.

No new axioms.
No sorry or admit.
No assumption of the desired speed inequality.

Candidate requiring Lean CI verification.
-/

/--
Multiplication by -i commutes with the
Jacobi inner product in its second argument.
-/
private theorem p76_5_inner_negI
    {n : ℕ}
    (w v : Fin n → ℂ) :
    jacobiInner w (fun j => -Complex.I * v j) =
      -Complex.I * jacobiInner w v := by
  unfold jacobiInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
Centering the energy does not change
the Krylov derivative channel.
-/
theorem p76_5_centered_velocity_inner
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ)
    (hnorm : jacobiNormSq u = 1) :
    jacobiInner
        (krylovCenteredState u)
        (fun j =>
          -Complex.I *
            (p76_centeredEnergy n a b u) j) =
      jacobiInner
        (krylovCenteredState u)
        (fun j =>
          -Complex.I *
            ((jacobiComplex n a b).mulVec u) j) := by
  rw [p76_5_inner_negI]
  rw [p76_5_inner_negI]
  rw [p76_4_centeredEnergy_inner n a b u hnorm]

#print axioms p76_5_centered_velocity_inner

end Lanzarini
