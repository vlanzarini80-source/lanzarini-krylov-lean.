
import P82_4c_PhysicalAccelerationBridge

namespace Lanzarini

/-!
P82.5: Physical second derivative of Krylov complexity.

Derived from the genuine Jacobi state,
velocity and acceleration.

No assumed Taylor coefficients.
No assumed deficit coefficient.
No new axioms.
No sorry or admit.

Candidate requiring Lean CI verification.
-/

/-- Physical acceleration expression for K''(t). -/
noncomputable def p82_5_Kddot
    (p q s delta t : ℝ) : ℝ :=
  2 * ∑ j : Fin 4,
    (j.val : ℝ) *
      ((star ((p81_2_velocity p q s delta t) j) *
          (p81_2_velocity p q s delta t j)).re +
       (star ((p81_2_state p q s delta t) j) *
          (p81_2b2_acceleration p q s delta t j)).re)

/--
Coordinate projection preserves the physical
derivative of a vector-valued trajectory.
-/
private theorem p82_5_component_derivative
    (f : ℝ → Fin 4 → ℂ)
    (df : Fin 4 → ℂ)
    (t : ℝ)
    (j : Fin 4)
    (hf : HasDerivAt f df t) :
    HasDerivAt
      (fun x : ℝ => f x j)
      (df j)
      t := by

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

  have h :=
    LC.hasFDerivAt.comp_hasDerivAt t hf

  exact h

/--
Derivative of the real part of a conjugate
product, obtained from the two coordinate
derivatives.
-/
private theorem p82_5_conjugate_product_derivative
    (f g : ℝ → ℂ)
    (df dg : ℂ)
    (t : ℝ)
    (hf : HasDerivAt f df t)
    (hg : HasDerivAt g dg t) :
    HasDerivAt
      (fun x : ℝ => (star (f x) * g x).re)
      ((star df * g t).re +
        (star (f t) * dg).re)
      t := by

  have hstar :
      HasDerivAt
        (fun x : ℝ => star (f x))
        (star df)
        t := by
    exact hf.star

  have hmul := hstar.mul hg

  have hre :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      t hmul

  convert hre using 1
  simp only [Complex.add_re]

/--
Genuine physical derivative of Kdot.

This derives K'' from the physical state,
velocity and acceleration.
-/
theorem p82_5_Kdot_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p82_4a_Kdot p q s delta)
      (p82_5_Kddot p q s delta t)
      t := by

  have hs :=
    p81_2_state_hasDerivAt
      p q s delta t

  have hv :=
    p82_4c_velocity_hasDerivAt
      p q s delta t

  have hterm (j : Fin 4) :
      HasDerivAt
        (fun x : ℝ =>
          (star ((p81_2_state p q s delta x) j) *
            (p81_2_velocity p q s delta x j)).re)
        ((star ((p81_2_velocity p q s delta t) j) *
            (p81_2_velocity p q s delta t j)).re +
         (star ((p81_2_state p q s delta t) j) *
            (p81_2b2_acceleration p q s delta t j)).re)
        t := by

    have hsj :=
      p82_5_component_derivative
        (p81_2_state p q s delta)
        (p81_2_velocity p q s delta t)
        t j hs

    have hvj :=
      p82_5_component_derivative
        (p81_2_velocity p q s delta)
        (p81_2b2_acceleration p q s delta t)
        t j hv

    exact
      p82_5_conjugate_product_derivative
        (fun x => (p81_2_state p q s delta x) j)
        (fun x => (p81_2_velocity p q s delta x) j)
        ((p81_2_velocity p q s delta t) j)
        ((p81_2b2_acceleration p q s delta t) j)
        t hsj hvj

  have hsum :
      HasDerivAt
        (fun x : ℝ =>
          ∑ j : Fin 4,
            (j.val : ℝ) *
              (star ((p81_2_state p q s delta x) j) *
                (p81_2_velocity p q s delta x j)).re)
        (∑ j : Fin 4,
          (j.val : ℝ) *
            ((star ((p81_2_velocity p q s delta t) j) *
                (p81_2_velocity p q s delta t j)).re +
             (star ((p81_2_state p q s delta t) j) *
                (p81_2b2_acceleration p q s delta t j)).re))
        t := by

    apply HasDerivAt.fun_sum
    intro j hj
    exact (hterm j).const_mul _

  have hfinal := hsum.const_mul (2 : ℝ)

  change
    HasDerivAt
      (fun x : ℝ =>
        2 * ∑ j : Fin 4,
          (j.val : ℝ) *
            (star ((p81_2_state p q s delta x) j) *
              (p81_2_velocity p q s delta x j)).re)
      (2 * ∑ j : Fin 4,
        (j.val : ℝ) *
          ((star ((p81_2_velocity p q s delta t) j) *
              (p81_2_velocity p q s delta t j)).re +
           (star ((p81_2_state p q s delta t) j) *
              (p81_2b2_acceleration p q s delta t j)).re))
      t

  exact hfinal

/--
Second derivative of physical Krylov
complexity, expressed through Kdot.
-/
theorem p82_5_physical_second_derivative
    (p q s delta t : ℝ) :
    HasDerivAt
      (p82_4a_Kdot p q s delta)
      (p82_5_Kddot p q s delta t)
      t := by
  exact p82_5_Kdot_hasDerivAt p q s delta t

#print axioms p82_5_Kdot_hasDerivAt
#print axioms p82_5_physical_second_derivative

end Lanzarini
