
import P84_4r6_PhysicalSecondDerivative

namespace Lanzarini

/-!
P84.4r7a: physical velocity second derivative.

Derived directly from the physical Jacobi evolution.
No expected Taylor coefficients.
-/

noncomputable def p84_4r7a_acceleration
    (p q r d e f t : ℝ)
    (j : Fin 4) : ℂ :=
  -Complex.I *
    ((jacobiComplex 4
      (p84_a d e f)
      (p84_b p q r)).mulVec
      (p84_4l_v p q r d e f t)) j

theorem p84_4r7a_velocity_derivative
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    deriv
      (fun s : ℝ =>
        p84_4l_v p q r d e f s j)
      t =
    p84_4r7a_acceleration p q r d e f t j := by
  exact
    (p84_4r6_velocity_hasDerivAt
      p q r d e f t j).deriv

theorem p84_4r7a_acceleration_hasDerivAt
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun s : ℝ =>
        p84_4r7a_acceleration p q r d e f s j)
      (-Complex.I *
        ((jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
          (p84_4r7a_acceleration p q r d e f t)) j)
      t := by

  let H := jacobiComplex 4
    (p84_a d e f)
    (p84_b p q r)

  have hterm (k : Fin 4) :
      HasDerivAt
        (fun s : ℝ =>
          H j k *
            p84_4l_v p q r d e f s k)
        (H j k *
          p84_4r7a_acceleration p q r d e f t k)
        t := by
    have hk :
        HasDerivAt
          (fun s : ℝ =>
            p84_4l_v p q r d e f s k)
          (p84_4r7a_acceleration
            p q r d e f t k)
          t := by
      exact
        p84_4r6_velocity_hasDerivAt
          p q r d e f t k

    exact hk.const_mul (H j k)

  have hsum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ k : Fin 4,
            H j k *
              p84_4l_v p q r d e f s k)
        (∑ k : Fin 4,
          H j k *
            p84_4r7a_acceleration
              p q r d e f t k)
        t := by
    simpa only [Fin.sum_univ_four] using
      (((hterm 0).add (hterm 1)).add
        (hterm 2)).add (hterm 3)

  have hscaled :=
    hsum.const_mul (-Complex.I)

  simpa only [
    p84_4r7a_acceleration,
    H,
    Matrix.mulVec,
    dotProduct
  ] using hscaled

theorem p84_4r7a_velocity_second_hasDerivAt
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun s : ℝ =>
        deriv
          (fun x : ℝ =>
            p84_4l_v p q r d e f x j)
          s)
      (-Complex.I *
        ((jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
          (p84_4r7a_acceleration p q r d e f t)) j)
      t := by

  have hfun :
      (fun s : ℝ =>
        deriv
          (fun x : ℝ =>
            p84_4l_v p q r d e f x j)
          s) =
      (fun s : ℝ =>
        p84_4r7a_acceleration
          p q r d e f s j) := by
    funext s
    exact p84_4r7a_velocity_derivative
      p q r d e f s j

  rw [hfun]

  exact
    p84_4r7a_acceleration_hasDerivAt
      p q r d e f t j

theorem p84_4r7a_velocity_second_derivative
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    deriv
      (fun s : ℝ =>
        deriv
          (fun x : ℝ =>
            p84_4l_v p q r d e f x j)
          s)
      t =
    -Complex.I *
      ((jacobiComplex 4
        (p84_a d e f)
        (p84_b p q r)).mulVec
        (p84_4r7a_acceleration p q r d e f t)) j := by
  exact
    (p84_4r7a_velocity_second_hasDerivAt
      p q r d e f t j).deriv

#print axioms p84_4r7a_velocity_derivative
#print axioms p84_4r7a_acceleration_hasDerivAt
#print axioms p84_4r7a_velocity_second_hasDerivAt
#print axioms p84_4r7a_velocity_second_derivative

end Lanzarini
