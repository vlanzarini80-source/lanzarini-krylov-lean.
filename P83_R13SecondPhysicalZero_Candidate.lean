
import P83_PhysicalInitialZeros_Candidate

namespace Lanzarini

/-!
P83: Second initial derivative of the
physical raw minor R13.

Derived from the Jacobi state,
velocity and acceleration.

No P79 coefficients are used.
No expected deficit coefficient is assumed.
No additional axioms.
Candidate requiring Lean CI verification.
-/

/-- Component derivative of a physical vector. -/
private theorem p83_r13_component_derivative
    (f : ℝ → Fin 4 → ℂ)
    (df : Fin 4 → ℂ)
    (t : ℝ)
    (j : Fin 4)
    (hf : HasDerivAt f df t) :
    HasDerivAt
      (fun x : ℝ => f x j)
      (df j) t := by

  let L : (Fin 4 → ℂ) →ₗ[ℝ] ℂ :=
    {
      toFun := fun v => v j
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl
    }

  let LC : (Fin 4 → ℂ) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap L

  exact LC.hasFDerivAt.comp_hasDerivAt t hf

/--
Acceleration differentiability obtained
by applying the fixed Jacobi generator
to the physical velocity derivative.
-/
private theorem p83_r13_acceleration_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p81_2b2_acceleration p q s delta)
      ((p81_2b1_generator p q s delta).mulVec
        (p81_2b2_acceleration p q s delta t))
      t := by

  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    p81_2b1_generator p q s delta

  let L :
      (Fin 4 → ℂ) →ₗ[ℝ] (Fin 4 → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ) A

  let LC :
      (Fin 4 → ℂ) →L[ℝ] (Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap L

  have hv :=
    p81_2b1_velocity_hasDerivAt
      p q s delta t

  change
    HasDerivAt
      (fun x : ℝ =>
        A.mulVec (p81_2_velocity p q s delta x))
      (A.mulVec
        (p81_2b2_acceleration p q s delta t))
      t

  exact LC.hasFDerivAt.comp_hasDerivAt t hv

/--
At the initial state, acceleration
at the third site vanishes.
-/
theorem p83_r13_initial_acceleration_site3
    (p q s delta : ℝ) :
    (p81_2b2_acceleration
      p q s delta 0) 3 = 0 := by

  change
    ((p81_2b1_generator p q s delta).mulVec
      (p81_2_velocity p q s delta 0)) 3 = 0

  rw [p81_2b1_generator_action]
  rw [p81_2b_velocity_at_zero]
  rw [p81_H_action]
  simp

/--
The second derivative of the physical
raw minor R13 vanishes at time zero.

No initial second derivative is assumed.
-/
theorem p83_physical_R13_second_zero
    (p q s delta : ℝ) :
    iteratedDeriv 2
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3)
      0 = 0 := by

  let u := p81_2_state p q s delta
  let v := p81_2_velocity p q s delta
  let a := p81_2b2_acceleration p q s delta

  have hs :=
    p81_2_state_hasDerivAt p q s delta 0

  have ha :=
    p83_r13_acceleration_hasDerivAt
      p q s delta 0

  have hs1 :=
    p83_r13_component_derivative
      u (v 0) 0 1 hs

  have hs3 :=
    p83_r13_component_derivative
      u (v 0) 0 3 hs

  have ha1 :=
    p83_r13_component_derivative
      a
      ((p81_2b1_generator p q s delta).mulVec
        (a 0))
      0 1 ha

  have ha3 :=
    p83_r13_component_derivative
      a
      ((p81_2b1_generator p q s delta).mulVec
        (a 0))
      0 3 ha

  have hu1 : u 0 1 = 0 := by
    change (p81_2_state p q s delta 0) 1 = 0
    rw [p81_2b_state_zero]
    rfl

  have hu3 : u 0 3 = 0 := by
    change (p81_2_state p q s delta 0) 3 = 0
    rw [p81_2b_state_zero]
    rfl

  have hv3 : v 0 3 = 0 := by
    change (p81_2_velocity p q s delta 0) 3 = 0
    rw [p81_2b_velocity_at_zero]
    rfl

  have ha3zero : a 0 3 = 0 :=
    p83_r13_initial_acceleration_site3
      p q s delta

  have hproduct :=
    (hs1.mul ha3).sub (hs3.mul ha1)

  have hzero :
      v 0 1 * a 0 3 +
        u 0 1 *
          ((p81_2b1_generator p q s delta).mulVec
            (a 0)) 3 -
        (v 0 3 * a 0 1 +
          u 0 3 *
            ((p81_2b1_generator p q s delta).mulVec
              (a 0)) 1) = 0 := by
    simp [hu1, hu3, hv3, ha3zero]

  have hphysical :
      HasDerivAt
        (fun t : ℝ =>
          u t 1 * a t 3 - u t 3 * a t 1)
        0 0 := by
    simpa only [hzero] using hproduct

  have hminor :
      deriv
        (fun t : ℝ =>
          p81_2b2_rawMinor
            p q s delta t 1 3) =
      (fun t : ℝ =>
        u t 1 * a t 3 - u t 3 * a t 1) := by
    funext t
    exact
      (p83_2_rawMinor_hasDerivAt
        p q s delta t 1 3).deriv

  rw [show (2 : ℕ) = 1 + 1 by decide]
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hminor]

  exact hphysical.deriv

#print axioms p83_r13_initial_acceleration_site3
#print axioms p83_physical_R13_second_zero

end Lanzarini
