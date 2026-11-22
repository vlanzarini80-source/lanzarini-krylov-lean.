
import P84_4r2d_CenteredPhysicalDerivative_Probe
import P84_4n_FirstMinorDerivativeReduction_Candidate

namespace Lanzarini

/-!
P84.4r3: discharge the physical derivative
hypothesis in P84.4n using P84.4r2d.

No expected Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

/-- The centered physical state has
    initial derivative equal to the
    physical velocity channel. -/
theorem p84_4r3_physical_derivative
    (p q r d e f : ℝ) :
    (fun k : Fin 4 =>
      deriv
        (fun t : ℝ =>
          p84_4l_u p q r d e f t k)
        0) =
    p84_4l_v p q r d e f 0 := by
  funext k
  exact
    (p84_4r2d_centered_hasDerivAt
      p q r d e f k).deriv

/-- The first physical minor derivative
    vanishes, assuming only the
    differentiability of v at zero. -/
theorem p84_4r3_first_minor_derivative
    (p q r d e f : ℝ)
    (i j : Fin 4)
    (hvj : HasDerivAt
      (fun t : ℝ =>
        p84_4l_v p q r d e f t j)
      (deriv
        (fun t : ℝ =>
          p84_4l_v p q r d e f t j)
        0) 0)
    (hvi : HasDerivAt
      (fun t : ℝ =>
        p84_4l_v p q r d e f t i)
      (deriv
        (fun t : ℝ =>
          p84_4l_v p q r d e f t i)
        0) 0) :
    deriv
      (fun t : ℝ =>
        p84_4l_minor p q r d e f t i j)
      0 = 0 := by

  have hui0 :=
    p84_4r2d_centered_hasDerivAt
      p q r d e f i

  have huj0 :=
    p84_4r2d_centered_hasDerivAt
      p q r d e f j

  have hui :
      HasDerivAt
        (fun t : ℝ =>
          p84_4l_u p q r d e f t i)
        (deriv
          (fun t : ℝ =>
            p84_4l_u p q r d e f t i)
          0) 0 := by
    simpa only [hui0.deriv] using hui0

  have huj :
      HasDerivAt
        (fun t : ℝ =>
          p84_4l_u p q r d e f t j)
        (deriv
          (fun t : ℝ =>
            p84_4l_u p q r d e f t j)
          0) 0 := by
    simpa only [huj0.deriv] using huj0

  exact
    p84_4n_first_minor_derivative_reduction
      p q r d e f i j
      (p84_4r3_physical_derivative
        p q r d e f)
      hui hvj huj hvi

#print axioms p84_4r3_physical_derivative
#print axioms p84_4r3_first_minor_derivative

end Lanzarini
