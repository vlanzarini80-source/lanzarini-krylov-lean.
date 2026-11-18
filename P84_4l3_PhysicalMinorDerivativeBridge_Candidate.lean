
import P84_4l2_GramMinorDerivative_Candidate

namespace Lanzarini

/-!
P84.4l.3: physical Gram minor derivative bridge.

The vectors come from the actual Jacobi evolution.
Differentiability is explicitly assumed here and
must be discharged in a subsequent theorem.

No expected coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/--
Derivative of a physical Gram minor at zero,
under explicit differentiability hypotheses.
-/
theorem p84_4l3_physical_minor_derivative
    (p q r d e f : ℝ)
    (i j : Fin 4)
    (hui : HasDerivAt
      (fun t => p84_4l_u p q r d e f t i)
      (deriv (fun t => p84_4l_u p q r d e f t i) 0) 0)
    (hvj : HasDerivAt
      (fun t => p84_4l_v p q r d e f t j)
      (deriv (fun t => p84_4l_v p q r d e f t j) 0) 0)
    (huj : HasDerivAt
      (fun t => p84_4l_u p q r d e f t j)
      (deriv (fun t => p84_4l_u p q r d e f t j) 0) 0)
    (hvi : HasDerivAt
      (fun t => p84_4l_v p q r d e f t i)
      (deriv (fun t => p84_4l_v p q r d e f t i) 0) 0) :
    deriv
      (fun t => p84_4l_minor p q r d e f t i j)
      0 =
      deriv (fun t => p84_4l_u p q r d e f t i) 0 *
        p84_4l_v p q r d e f 0 j -
      deriv (fun t => p84_4l_u p q r d e f t j) 0 *
        p84_4l_v p q r d e f 0 i := by

  have hzero_i :
      p84_4l_u p q r d e f 0 i = 0 := by
    have h := p84_4l1_u_zero p q r d e f
    exact congrFun h i

  have hzero_j :
      p84_4l_u p q r d e f 0 j = 0 := by
    have h := p84_4l1_u_zero p q r d e f
    exact congrFun h j

  have hformula :
      (fun t => p84_4l_minor p q r d e f t i j) =
      (fun t =>
        p84_4l_u p q r d e f t i *
          p84_4l_v p q r d e f t j -
        p84_4l_u p q r d e f t j *
          p84_4l_v p q r d e f t i) := by
    funext t
    exact p84_4l_minor_formula p q r d e f t i j

  rw [hformula]

  exact p84_4l2_minor_derivative_at_zero
    (fun t => p84_4l_u p q r d e f t i)
    (fun t => p84_4l_v p q r d e f t j)
    (fun t => p84_4l_u p q r d e f t j)
    (fun t => p84_4l_v p q r d e f t i)
    hui hvj huj hvi hzero_i hzero_j

#print axioms p84_4l3_physical_minor_derivative

end Lanzarini
