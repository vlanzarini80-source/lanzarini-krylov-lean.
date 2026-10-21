
import P74_2_KrylovDerivative

namespace Lanzarini

/--
P75.1: Orthogonality of a normalized finite state
to its centered Krylov-number state.

The result is derived from existing definitions
and the normalization hypothesis.

No physical evolution or desired conclusion
is assumed as a hypothesis.
-/
theorem p75_centeredState_orthogonal
    {n : ℕ} (psi : Fin n → ℂ)
    (hnorm : jacobiNormSq psi = 1) :
    jacobiInner psi (krylovCenteredState psi) = 0 := by

  have hcenter :
      jacobiInner psi (krylovCenteredState psi) =
        jacobiInner psi
          ((krylovNumberOperator n).mulVec psi) -
        (krylovComplexity psi : ℂ) *
          jacobiInner psi psi := by
    unfold jacobiInner krylovCenteredState
    rw [krylovNumberOperator_mulVec]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring

  rw [hcenter, krylovComplexity_expectation,
      jacobiInner_self, hnorm]
  simp

#print axioms p75_centeredState_orthogonal

end Lanzarini
