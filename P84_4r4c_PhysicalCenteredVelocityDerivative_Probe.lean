
import P84_4r4a_PhysicalEnergyMeanZero_Probe
import P84_4r4b_PhysicalVelocityDerivative_Probe

namespace Lanzarini

theorem p84_4r4c_energy_mean_hasDerivAt
    (p q r d e f : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        p76_energyMean 4
          (p84_a d e f)
          (p84_b p q r)
          (p84_4l_psi p q r d e f t))
      0 0 := by

  have hfun :
      (fun t : ℝ =>
        p76_energyMean 4
          (p84_a d e f)
          (p84_b p q r)
          (p84_4l_psi p q r d e f t)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact p84_4r4a_energy_mean_zero
      p q r d e f t

  rw [hfun]
  exact hasDerivAt_const 0 (0 : ℝ)


theorem p84_4r4c_velocity_uncentered
    (p q r d e f t : ℝ)
    (j : Fin 4) :
    p84_4l_v p q r d e f t j =
      -Complex.I *
        ((jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
          (p84_4l_psi p q r d e f t)) j := by

  unfold p84_4l_v p76_centeredEnergy

  rw [p84_4r4a_energy_mean_zero
    p q r d e f t]

  simp


theorem p84_4r4c_velocity_hasDerivAt
    (p q r d e f : ℝ)
    (j : Fin 4) :
    HasDerivAt
      (fun t : ℝ =>
        p84_4l_v p q r d e f t j)
      (-Complex.I *
        ((jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
          (p84_4l_v p q r d e f 0)) j)
      0 := by

  let H := jacobiComplex 4
    (p84_a d e f)
    (p84_b p q r)

  have hterm (k : Fin 4) :
      HasDerivAt
        (fun t : ℝ =>
          H j k *
            p84_4l_psi p q r d e f t k)
        (H j k *
          p84_4l_v p q r d e f 0 k)
        0 := by
    exact
      (p84_4r4b_psi_derivative
        p q r d e f k).const_mul (H j k)

  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ k : Fin 4,
            H j k *
              p84_4l_psi p q r d e f t k)
        (∑ k : Fin 4,
          H j k *
            p84_4l_v p q r d e f 0 k)
        0 := by

    simpa only [Fin.sum_univ_four] using
      (((hterm 0).add (hterm 1)).add
        (hterm 2)).add (hterm 3)

  have hscaled :=
    hsum.const_mul (-Complex.I)

  have hfun :
      (fun t : ℝ =>
        p84_4l_v p q r d e f t j) =
      (fun t : ℝ =>
        -Complex.I *
          ∑ k : Fin 4,
            H j k *
              p84_4l_psi p q r d e f t k) := by
    funext t
    rw [p84_4r4c_velocity_uncentered
      p q r d e f t j]
    rfl

  rw [hfun]

  simpa [H, Matrix.mulVec, dotProduct]
    using hscaled


theorem p84_4r4c_velocity_derivative
    (p q r d e f : ℝ)
    (j : Fin 4) :
    deriv
      (fun t : ℝ =>
        p84_4l_v p q r d e f t j)
      0 =
      -Complex.I *
        ((jacobiComplex 4
          (p84_a d e f)
          (p84_b p q r)).mulVec
          (p84_4l_v p q r d e f 0)) j := by

  exact
    (p84_4r4c_velocity_hasDerivAt
      p q r d e f j).deriv

#print axioms p84_4r4c_energy_mean_hasDerivAt
#print axioms p84_4r4c_velocity_uncentered
#print axioms p84_4r4c_velocity_hasDerivAt
#print axioms p84_4r4c_velocity_derivative

end Lanzarini
