
import P81_2b3_CenteredMinorDerivative

namespace Lanzarini

/-!
P81.2b3 Stage B1.

Exact algebraic bridge for the physical
centered Gram minor.

The state and velocity are those of the
actual four-dimensional Jacobi evolution.

No Taylor coefficients are assumed.
No deficit formula is assumed.
No additional mathematical assumptions.
-/

/-- Physical centered Gram coordinate. -/
noncomputable def p81_2b3b_centeredMinor
    (p q s delta t : ℝ)
    (i j : Fin 4) : ℂ :=
  krylovGramCoordinate
    (krylovCenteredState
      (p81_2_state p q s delta t))
    (p81_2_velocity p q s delta t)
    i j

/--
The new coordinate is exactly the
previously defined physical minor.
-/
theorem p81_2b3b_centeredMinor_eq
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    p81_2b3b_centeredMinor
      p q s delta t i j =
    p81_2_minor p q s delta t i j := by
  rfl

/--
Exact decomposition into the uncentered
minor and the Krylov-mean correction.
-/
theorem p81_2b3b_centeredMinor_decomposition
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    p81_2b3b_centeredMinor
      p q s delta t i j =
      ((i.val : ℂ) *
          (p81_2_state p q s delta t) i *
          (p81_2_velocity p q s delta t) j -
        (j.val : ℂ) *
          (p81_2_state p q s delta t) j *
          (p81_2_velocity p q s delta t) i) -
      (p81_2b3_K p q s delta t : ℂ) *
        p81_2b2_rawMinor
          p q s delta t i j := by

  change
    krylovGramCoordinate
      (krylovCenteredState
        (p81_2_state p q s delta t))
      (p81_2_velocity p q s delta t)
      i j =
      ((i.val : ℂ) *
          (p81_2_state p q s delta t) i *
          (p81_2_velocity p q s delta t) j -
        (j.val : ℂ) *
          (p81_2_state p q s delta t) j *
          (p81_2_velocity p q s delta t) i) -
      (krylovComplexity
        (p81_2_state p q s delta t) : ℂ) *
        ((p81_2_state p q s delta t) i *
          (p81_2_velocity p q s delta t) j -
         (p81_2_state p q s delta t) j *
          (p81_2_velocity p q s delta t) i)

  exact p81_2_minor_algebra
    (p81_2_state p q s delta t)
    (p81_2_velocity p q s delta t)
    i j

#print axioms p81_2b3b_centeredMinor_eq
#print axioms p81_2b3b_centeredMinor_decomposition

end Lanzarini
