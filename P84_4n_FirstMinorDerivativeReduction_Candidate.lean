
import P84_4m_InitialEnergyChannel_Candidate

namespace Lanzarini

/-!
P84.4n: reduction of the first physical
Gram-minor derivative to the physical
initial derivative identity.

All six Jacobi parameters remain free.

The physical identity u'(0) = v(0)
is an explicit outstanding hypothesis,
not a proven conclusion of this file.

No assumed Taylor coefficients.
No P79.
No sorry, admit, or new axioms.
-/

theorem p84_4n_first_minor_derivative_reduction
    (p q r d e f : ℝ)
    (i j : Fin 4)
    (hphysical :
      (fun k : Fin 4 =>
        deriv
          (fun t : ℝ =>
            p84_4l_u p q r d e f t k)
          0) =
      p84_4l_v p q r d e f 0)
    (hui : HasDerivAt
      (fun t => p84_4l_u p q r d e f t i)
      (deriv
        (fun t => p84_4l_u p q r d e f t i)
        0) 0)
    (hvj : HasDerivAt
      (fun t => p84_4l_v p q r d e f t j)
      (deriv
        (fun t => p84_4l_v p q r d e f t j)
        0) 0)
    (huj : HasDerivAt
      (fun t => p84_4l_u p q r d e f t j)
      (deriv
        (fun t => p84_4l_u p q r d e f t j)
        0) 0)
    (hvi : HasDerivAt
      (fun t => p84_4l_v p q r d e f t i)
      (deriv
        (fun t => p84_4l_v p q r d e f t i)
        0) 0) :
    deriv
      (fun t =>
        p84_4l_minor p q r d e f t i j)
      0 = 0 := by

  have hformula :=
    p84_4l3_physical_minor_derivative
      p q r d e f i j
      hui hvj huj hvi

  have hi :
      deriv
        (fun t : ℝ =>
          p84_4l_u p q r d e f t i)
        0 =
      p84_4l_v p q r d e f 0 i :=
    congrFun hphysical i

  have hj :
      deriv
        (fun t : ℝ =>
          p84_4l_u p q r d e f t j)
        0 =
      p84_4l_v p q r d e f 0 j :=
    congrFun hphysical j

  rw [hformula, hi, hj]
  ring

#print axioms p84_4n_first_minor_derivative_reduction

end Lanzarini
