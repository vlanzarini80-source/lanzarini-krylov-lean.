import P84_4r5_ClosedPhysicalMinorDerivative

namespace Lanzarini

/-!
P84.4r6: physical second derivatives.

Use the existing verified component derivative
of the physical Jacobi evolution.

No expected Taylor coefficients.
-/

theorem p84_4r6_psi_hasDerivAt
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun s : ℝ =>
        p84_4l_psi p q r d e f s j)
      (p84_4l_v p q r d e f t j)
      t := by

  have h :=
    p74_jacobiState_component_hasDerivAt
      4
      (p84_a d e f)
      (p84_b p q r)
      t p81_e0 j

  rw [p84_4r4c_velocity_uncentered
    p q r d e f t j]

  simpa [p84_4l_psi, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]
    using h


theorem p84_4r6_psi_derivative
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    deriv
      (fun s : ℝ =>
        p84_4l_psi p q r d e f s j)
      t =
    p84_4l_v p q r d e f t j := by

  exact
    (p84_4r6_psi_hasDerivAt
      p q r d e f t j).deriv


theorem p84_4r6_velocity_hasDerivAt
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun s : ℝ =>
        p84_4l_v p q r d e f s j)
      (-Complex.I *
        ((jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
          (p84_4l_v p q r d e f t)) j)
      t := by

  let H := jacobiComplex 4
    (p84_a d e f)
    (p84_b p q r)

  have hterm (k : Fin 4) :
      HasDerivAt
        (fun s : ℝ =>
          H j k *
            p84_4l_psi p q r d e f s k)
        (H j k *
          p84_4l_v p q r d e f t k)
        t := by

    exact
      (p84_4r6_psi_hasDerivAt
        p q r d e f t k).const_mul (H j k)

  have hsum :
      HasDerivAt
        (fun s : ℝ =>
          ∑ k : Fin 4,
            H j k *
              p84_4l_psi p q r d e f s k)
        (∑ k : Fin 4,
          H j k *
            p84_4l_v p q r d e f t k)
        t := by

    simpa only [Fin.sum_univ_four] using
      (((hterm 0).add (hterm 1)).add
        (hterm 2)).add (hterm 3)

  have hscaled :=
    hsum.const_mul (-Complex.I)

  have hfun :
      (fun s : ℝ =>
        p84_4l_v p q r d e f s j) =
      (fun s : ℝ =>
        -Complex.I *
          ∑ k : Fin 4,
            H j k *
              p84_4l_psi p q r d e f s k) := by

    funext s

    rw [p84_4r4c_velocity_uncentered
      p q r d e f s j]

    rfl

  rw [hfun]

  simpa [H, Matrix.mulVec, dotProduct]
    using hscaled


theorem p84_4r6_psi_second_derivative
    (p q r d e f : ℝ)
    (j : Fin 4) :
    deriv
      (fun t : ℝ =>
        deriv
          (fun s : ℝ =>
            p84_4l_psi p q r d e f s j)
          t)
      0 =
    -Complex.I *
      ((jacobiComplex 4
        (p84_a d e f)
        (p84_b p q r)).mulVec
        (p84_4l_v p q r d e f 0)) j := by

  have hfun :
      (fun t : ℝ =>
        deriv
          (fun s : ℝ =>
            p84_4l_psi p q r d e f s j)
          t) =
      (fun t : ℝ =>
        p84_4l_v p q r d e f t j) := by

    funext t

    exact
      p84_4r6_psi_derivative
        p q r d e f t j

  rw [hfun]

  exact
    (p84_4r6_velocity_hasDerivAt
      p q r d e f 0 j).deriv


#print axioms p84_4r6_psi_hasDerivAt
#print axioms p84_4r6_psi_derivative
#print axioms p84_4r6_velocity_hasDerivAt
#print axioms p84_4r6_psi_second_derivative

end Lanzarini
