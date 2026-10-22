
import P76_3_EnergySecondMoment

namespace Lanzarini

/-!
P76.4a: Centered energy and Krylov orthogonality.

First stage of the centered energy speed bound.

No new axioms.
No sorry.
No assumption of the desired speed inequality.

Candidate requiring Lean CI verification.
-/

/--
Linearity of the Jacobi inner product in its
second argument, for subtraction of a scalar
multiple of a vector.
-/
private theorem p76_4_inner_sub_scalar
    {n : ℕ}
    (w u v : Fin n → ℂ)
    (z : ℂ) :
    jacobiInner w
        (fun j => v j - z * u j) =
      jacobiInner w v -
        z * jacobiInner w u := by
  unfold jacobiInner
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
Orthogonality of the centered Krylov state
in the reversed inner-product order.

Derived from P75.1 by conjugate symmetry.
-/
theorem p76_4_centeredState_orthogonal_left
    {n : ℕ}
    (u : Fin n → ℂ)
    (hnorm : jacobiNormSq u = 1) :
    jacobiInner (krylovCenteredState u) u = 0 := by
  have h :=
    p75_centeredState_orthogonal u hnorm
  have hs :
      star (jacobiInner u (krylovCenteredState u)) =
        jacobiInner (krylovCenteredState u) u := by
    unfold jacobiInner
    simp only [map_sum, star_mul', star_star]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [h] at hs
  exact hs.symm

/--
Removing the energy expectation from Hu
does not change its inner product with the
centered Krylov state.
-/
theorem p76_4_centeredEnergy_inner
    (n : ℕ)
    (a b : Fin n → ℝ)
    (u : Fin n → ℂ)
    (hnorm : jacobiNormSq u = 1) :
    jacobiInner
        (krylovCenteredState u)
        (p76_centeredEnergy n a b u) =
      jacobiInner
        (krylovCenteredState u)
        ((jacobiComplex n a b).mulVec u) := by
  unfold p76_centeredEnergy
  rw [p76_4_inner_sub_scalar]
  rw [p76_4_centeredState_orthogonal_left u hnorm]
  simp

#print axioms p76_4_centeredState_orthogonal_left
#print axioms p76_4_centeredEnergy_inner

end Lanzarini
