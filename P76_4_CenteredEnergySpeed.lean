
import P76_3_EnergySecondMoment

namespace Lanzarini

/-!
P76.4a: Centered energy and Krylov orthogonality.

No new axioms.
No sorry or admit.
No assumption of the desired conclusion.

Candidate requiring Lean CI verification.
-/

/--
Linearity of the Jacobi inner product
in its second argument.
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
Conjugate symmetry of the Jacobi inner product.
-/
private theorem p76_4_inner_conj_symm
    {n : ℕ}
    (u v : Fin n → ℂ) :
    star (jacobiInner u v) =
      jacobiInner v u := by
  unfold jacobiInner
  simp only [star_sum, star_mul', star_star]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
The centered Krylov state is orthogonal
to the original normalized state,
with reversed arguments.
-/
theorem p76_4_centeredState_orthogonal_left
    {n : ℕ}
    (u : Fin n → ℂ)
    (hnorm : jacobiNormSq u = 1) :
    jacobiInner (krylovCenteredState u) u = 0 := by
  have h :
      jacobiInner u (krylovCenteredState u) = 0 :=
    p75_centeredState_orthogonal u hnorm

  have hsym :
      star (jacobiInner u (krylovCenteredState u)) =
        jacobiInner (krylovCenteredState u) u :=
    p76_4_inner_conj_symm u (krylovCenteredState u)

  calc
    jacobiInner (krylovCenteredState u) u =
        star (jacobiInner u (krylovCenteredState u)) :=
          hsym.symm
    _ = 0 := by
      simpa using congrArg star h

/--
Subtracting the mean energy from Hu
does not change its inner product with
the centered Krylov state.
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

#print axioms p76_4_inner_conj_symm
#print axioms p76_4_centeredState_orthogonal_left
#print axioms p76_4_centeredEnergy_inner

end Lanzarini
