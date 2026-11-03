
import P83_2_PhysicalMinorAcceleration
import P81_2b3b_CenteredMinorBridge

namespace Lanzarini

/-!
P83.3: Centered physical Gram derivative bridge.

The centering correction is differentiated
using the genuine Krylov derivative and
the physical raw-minor derivative.

The weighted-minor derivative is kept
as an explicit prerequisite for the
complete centered-minor derivative.

No coefficient from P79 is used.
No deficit coefficient is assumed.
-/

/-- Weighted physical minor. -/
noncomputable def p83_3_weightedMinor
    (p q s delta t : ℝ)
    (i j : Fin 4) : ℂ :=
  (i.val : ℂ) *
      (p81_2_state p q s delta t) i *
      (p81_2_velocity p q s delta t) j -
    (j.val : ℂ) *
      (p81_2_state p q s delta t) j *
      (p81_2_velocity p q s delta t) i

/-- Actual Krylov-centering correction. -/
noncomputable def p83_3_centerCorrection
    (p q s delta t : ℝ)
    (i j : Fin 4) : ℂ :=
  (p81_2b3_K p q s delta t : ℂ) *
    p81_2b2_rawMinor p q s delta t i j

/--
Exact connection to the physical
centered Gram coordinate.
-/
theorem p83_3_centered_decomposition
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    p81_2b3b_centeredMinor
        p q s delta t i j =
      p83_3_weightedMinor
        p q s delta t i j -
      p83_3_centerCorrection
        p q s delta t i j := by
  rw [p81_2b3b_centeredMinor_decomposition]
  rfl

/--
Physical derivative of the centering
correction K(t) times R_ij(t).
-/
theorem p83_3_centerCorrection_hasDerivAt
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    HasDerivAt
      (fun x : ℝ =>
        p83_3_centerCorrection
          p q s delta x i j)
      ((p82_4a_Kdot
          p q s delta t : ℂ) *
        p81_2b2_rawMinor
          p q s delta t i j +
       (p81_2b3_K
          p q s delta t : ℂ) *
        ((p81_2_state
            p q s delta t) i *
          (p81_2b2_acceleration
            p q s delta t) j -
         (p81_2_state
            p q s delta t) j *
          (p81_2b2_acceleration
            p q s delta t) i))
      t := by
  have hK :=
    p82_4a_K_derivative
      p q s delta t

  have hKC := hK.ofReal_comp

  have hR :=
    p83_2_rawMinor_hasDerivAt
      p q s delta t i j

  simpa only [p83_3_centerCorrection]
    using hKC.mul hR

/--
The complete centered derivative follows
from the derivative of the weighted
physical minor.

The weighted derivative remains a
separate mathematical obligation.
-/
theorem p83_3_centered_hasDerivAt_of_weighted
    (p q s delta t : ℝ)
    (i j : Fin 4)
    (dA : ℂ)
    (hA :
      HasDerivAt
        (fun x : ℝ =>
          p83_3_weightedMinor
            p q s delta x i j)
        dA t) :
    HasDerivAt
      (fun x : ℝ =>
        p81_2b3b_centeredMinor
          p q s delta x i j)
      (dA -
        ((p82_4a_Kdot
            p q s delta t : ℂ) *
          p81_2b2_rawMinor
            p q s delta t i j +
         (p81_2b3_K
            p q s delta t : ℂ) *
          ((p81_2_state
              p q s delta t) i *
            (p81_2b2_acceleration
              p q s delta t) j -
           (p81_2_state
              p q s delta t) j *
            (p81_2b2_acceleration
              p q s delta t) i)))
      t := by

  have hC :=
    p83_3_centerCorrection_hasDerivAt
      p q s delta t i j

  have hEq :
      (fun x : ℝ =>
        p81_2b3b_centeredMinor
          p q s delta x i j) =
      (fun x : ℝ =>
        p83_3_weightedMinor
          p q s delta x i j -
        p83_3_centerCorrection
          p q s delta x i j) := by
    funext x
    exact p83_3_centered_decomposition
      p q s delta x i j

  rw [hEq]
  exact hA.sub hC

#print axioms p83_3_centered_decomposition
#print axioms p83_3_centerCorrection_hasDerivAt
#print axioms p83_3_centered_hasDerivAt_of_weighted

end Lanzarini
