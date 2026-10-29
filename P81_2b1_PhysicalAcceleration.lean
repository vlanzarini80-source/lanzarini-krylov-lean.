import P81_2b_InitialPhysicalData

namespace Lanzarini

/-!
P81.2b.1 - Physical velocity and acceleration.

Derived from the actual four-site Jacobi
evolution.

No assumed Gram-minor coefficients.
No assumed deficit coefficient.

Candidate requiring Lean CI verification.
-/

/-- Physical Jacobi time generator. -/
noncomputable def p81_2b1_generator
    (p q s delta : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  (-Complex.I) • p81_H p q s delta

/-- Its action is exactly multiplication by -iH. -/
theorem p81_2b1_generator_action
    (p q s delta : ℝ)
    (u : Fin 4 → ℂ) :
    (p81_2b1_generator p q s delta).mulVec u =
      (fun j : Fin 4 =>
        -Complex.I *
          ((p81_H p q s delta).mulVec u) j) := by
  funext j
  simp [
    p81_2b1_generator,
    Matrix.mulVec,
    dotProduct,
    Finset.mul_sum,
    mul_assoc
  ]

/-- Connect generator and existing physical velocity. -/
theorem p81_2b1_velocity_eq_generator
    (p q s delta t : ℝ) :
    p81_2_velocity p q s delta t =
      (p81_2b1_generator p q s delta).mulVec
        (p81_2_state p q s delta t) := by
  unfold p81_2_velocity
  exact
    (p81_2b1_generator_action
      p q s delta
      (p81_2_state p q s delta t)).symm

/--
Genuine derivative of physical velocity.

Uses the already verified state derivative
and the continuous real-linear action
of a fixed matrix.
-/
theorem p81_2b1_velocity_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p81_2_velocity p q s delta)
      ((p81_2b1_generator p q s delta).mulVec
        (p81_2_velocity p q s delta t))
      t := by

  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    p81_2b1_generator p q s delta

  let L :
      (Fin 4 → ℂ) →ₗ[ℝ] (Fin 4 → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ) A

  let LC :
      (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap L

  have hs :=
    p81_2_state_hasDerivAt p q s delta t

  have hd :
      HasDerivAt
        (fun x : ℝ =>
          A.mulVec
            (p81_2_state p q s delta x))
        (A.mulVec
          (p81_2_velocity p q s delta t))
        t := by
    exact
      LC.hasFDerivAt.comp_hasDerivAt t hs

  have heq :
      (fun x : ℝ =>
        A.mulVec
          (p81_2_state p q s delta x)) =
        p81_2_velocity p q s delta := by

    funext x

    change
      (p81_2b1_generator p q s delta).mulVec
        (p81_2_state p q s delta x) =
      p81_2_velocity p q s delta x

    exact
      (p81_2b1_velocity_eq_generator
        p q s delta x).symm

  rw [heq] at hd
  exact hd

/--
Initial acceleration obtained from
the real physical velocity.

No Taylor coefficient is assumed.
-/
theorem p81_2b1_initial_acceleration
    (p q s delta : ℝ) :
    HasDerivAt
      (p81_2_velocity p q s delta)
      ((p81_2b1_generator p q s delta).mulVec
        ![0, -Complex.I * (p : ℂ), 0, 0])
      0 := by

  have h :=
    p81_2b1_velocity_hasDerivAt
      p q s delta 0

  rw [p81_2b_velocity_at_zero] at h
  exact h

#print axioms p81_2b1_generator_action
#print axioms p81_2b1_velocity_eq_generator
#print axioms p81_2b1_velocity_hasDerivAt
#print axioms p81_2b1_initial_acceleration

end Lanzarini
