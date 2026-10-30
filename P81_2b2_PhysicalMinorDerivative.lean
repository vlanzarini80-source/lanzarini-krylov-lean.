
import P81_2b1_PhysicalAcceleration

namespace Lanzarini

/-!
P81.2b.2 - Physical Gram-coordinate derivative.

Derivation from the actual Jacobi state
and its physical velocity.

No assumed Taylor coefficients.
No assumed deficit coefficients.
No sorry, admit, or new axioms.
-/

/-- Physical acceleration. -/
noncomputable def p81_2b2_acceleration
    (p q s delta t : ℝ) : Fin 4 → ℂ :=
  (p81_2b1_generator p q s delta).mulVec
    (p81_2_velocity p q s delta t)

/-- Raw physical Gram coordinate. -/
noncomputable def p81_2b2_rawMinor
    (p q s delta t : ℝ)
    (i j : Fin 4) : ℂ :=
  krylovGramCoordinate
    (p81_2_state p q s delta t)
    (p81_2_velocity p q s delta t)
    i j

/--
Coordinate derivative obtained by composition
with a continuous real-linear projection.
-/
private theorem p81_2b2_coordinate_derivative
    (f : ℝ → Fin 4 → ℂ)
    (df : Fin 4 → ℂ)
    (t : ℝ)
    (i : Fin 4)
    (hf : HasDerivAt f df t) :
    HasDerivAt
      (fun x : ℝ => f x i)
      (df i)
      t := by

  let L : (Fin 4 → ℂ) →ₗ[ℝ] ℂ :=
    {
      toFun := fun v => v i
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl
    }

  let LC : (Fin 4 → ℂ) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap L

  have h :
      HasDerivAt
        (fun x : ℝ => LC (f x))
        (LC df)
        t :=
    LC.hasFDerivAt.comp_hasDerivAt t hf

  exact h

/--
Derivative of the raw physical minor.

This uses the genuine state and velocity
derivatives and the verified product rule.
-/
theorem p81_2b2_rawMinor_hasDerivAt
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    HasDerivAt
      (fun x : ℝ =>
        p81_2b2_rawMinor p q s delta x i j)
      ((p81_2_velocity p q s delta t) i *
          (p81_2_velocity p q s delta t) j +
        (p81_2_state p q s delta t) i *
          (p81_2b2_acceleration p q s delta t) j -
        ((p81_2_velocity p q s delta t) j *
            (p81_2_velocity p q s delta t) i +
          (p81_2_state p q s delta t) j *
            (p81_2b2_acceleration p q s delta t) i))
      t := by

  have hs :=
    p81_2_state_hasDerivAt
      p q s delta t

  have hv :=
    p81_2b1_velocity_hasDerivAt
      p q s delta t

  have hsi :=
    p81_2b2_coordinate_derivative
      (p81_2_state p q s delta)
      (p81_2_velocity p q s delta t)
      t i hs

  have hsj :=
    p81_2b2_coordinate_derivative
      (p81_2_state p q s delta)
      (p81_2_velocity p q s delta t)
      t j hs

  have hvi :=
    p81_2b2_coordinate_derivative
      (p81_2_velocity p q s delta)
      (p81_2b2_acceleration p q s delta t)
      t i hv

  have hvj :=
    p81_2b2_coordinate_derivative
      (p81_2_velocity p q s delta)
      (p81_2b2_acceleration p q s delta t)
      t j hv

  change
    HasDerivAt
      (fun x : ℝ =>
        krylovGramCoordinate
          (p81_2_state p q s delta x)
          (p81_2_velocity p q s delta x)
          i j)
      _
      t

  exact
    p81_2_minor_product_rule
      (p81_2_state p q s delta)
      (p81_2_velocity p q s delta)
      (p81_2_velocity p q s delta t)
      (p81_2b2_acceleration p q s delta t)
      t i j hsi hsj hvi hvj

#print axioms p81_2b2_rawMinor_hasDerivAt

end Lanzarini
