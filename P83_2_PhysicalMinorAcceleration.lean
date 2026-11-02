
import P83_1_PhysicalGramJets

namespace Lanzarini

/-!
P83.2: Physical minor acceleration bridge.

The derivative is obtained from the genuine
Jacobi state, velocity, and acceleration.

The two velocity-product terms cancel
algebraically.

No coefficient from P79 is used.
No desired deficit coefficient is assumed.
-/

/--
The derivative of the raw physical Gram
coordinate is an antisymmetric product
of state and physical acceleration.
-/
theorem p83_2_rawMinor_hasDerivAt
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    HasDerivAt
      (fun x : ℝ =>
        p81_2b2_rawMinor
          p q s delta x i j)
      ((p81_2_state p q s delta t) i *
          (p81_2b2_acceleration
            p q s delta t) j -
        (p81_2_state p q s delta t) j *
          (p81_2b2_acceleration
            p q s delta t) i)
      t := by
  have h :=
    p81_2b2_rawMinor_hasDerivAt
      p q s delta t i j
  convert h using 1 <;> ring

/--
The first derivative of the raw
coordinate (1,2) vanishes initially.
-/
theorem p83_2_rawMinor12_initial_derivative
    (p q s delta : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 2)
      0
      0 := by
  have h :=
    p83_2_rawMinor_hasDerivAt
      p q s delta 0 1 2
  rw [p81_2b_state_zero] at h
  simpa [p81_e0] using h

/--
The first derivative of the raw
coordinate (1,3) vanishes initially.
-/
theorem p83_2_rawMinor13_initial_derivative
    (p q s delta : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        p81_2b2_rawMinor
          p q s delta t 1 3)
      0
      0 := by
  have h :=
    p83_2_rawMinor_hasDerivAt
      p q s delta 0 1 3
  rw [p81_2b_state_zero] at h
  simpa [p81_e0] using h

#print axioms p83_2_rawMinor_hasDerivAt
#print axioms p83_2_rawMinor12_initial_derivative
#print axioms p83_2_rawMinor13_initial_derivative

end Lanzarini
