
import P81_1_JacobiPhysicalPowers

namespace Lanzarini

/-!
P81.2a: Physical Gram-minor bridge.

Starting point:
- Actual Jacobi evolution
- Physical Hamiltonian P81.1
- Energy conservation P77.2
- Physical derivative P73.2

No P79 coefficient formulas are assumed.
No expected Taylor coefficients are used.

No new axioms or proof placeholders.

Candidate requiring Lean CI verification.
-/

/-- Physical Jacobi evolution. -/
noncomputable def p81_2_state
    (p q s delta : ℝ)
    (t : ℝ) : Fin 4 → ℂ :=
  jacobiState 4
    (p81_a delta)
    (p81_b p q s)
    t p81_e0

/-- Velocity obtained from the Hamiltonian. -/
noncomputable def p81_2_velocity
    (p q s delta : ℝ)
    (t : ℝ) : Fin 4 → ℂ :=
  fun j =>
    -Complex.I *
      ((p81_H p q s delta).mulVec
        (p81_2_state p q s delta t)) j

/--
The energy expectation is identically zero
for this initial state and Hamiltonian.

This follows from the previously proven
conservation law.
-/
theorem p81_2_energyMean_zero
    (p q s delta t : ℝ) :
    p76_energyMean 4
      (p81_a delta)
      (p81_b p q s)
      (p81_2_state p q s delta t) = 0 := by

  change
    p76_energyMean 4
      (p81_a delta)
      (p81_b p q s)
      (jacobiState 4
        (p81_a delta)
        (p81_b p q s)
        t p81_e0) = 0

  rw [p77_2_energyMean_conserved]

  change
    (jacobiInner p81_e0
      ((p81_H p q s delta).mulVec
        p81_e0)).re = 0

  rw [p81_H1]

  simp [
    jacobiInner,
    p81_e0,
    Fin.sum_univ_succ
  ]

/--
Centered energy velocity coincides
with the physical Jacobi velocity.

Zero mean energy is proved above,
not introduced as an assumption.
-/
theorem p81_2_centeredVelocity_eq
    (p q s delta t : ℝ) :
    (fun j : Fin 4 =>
      -Complex.I *
        (p76_centeredEnergy 4
          (p81_a delta)
          (p81_b p q s)
          (p81_2_state p q s delta t)) j) =
    p81_2_velocity p q s delta t := by

  funext j

  change
    -Complex.I *
      (((p81_H p q s delta).mulVec
          (p81_2_state p q s delta t)) j -
        (p76_energyMean 4
          (p81_a delta)
          (p81_b p q s)
          (p81_2_state p q s delta t) : ℂ) *
        (p81_2_state p q s delta t) j) =
      -Complex.I *
        ((p81_H p q s delta).mulVec
          (p81_2_state p q s delta t)) j

  rw [p81_2_energyMean_zero p q s delta t]
  ring

/--
Gram minor constructed from the
actual physical Jacobi evolution.
-/
noncomputable def p81_2_minor
    (p q s delta t : ℝ)
    (i j : Fin 4) : ℂ :=
  krylovGramCoordinate
    (krylovCenteredState
      (p81_2_state p q s delta t))
    (p81_2_velocity p q s delta t)
    i j

/--
Identity between the physical Gram minor
and the centered-energy Gram minor
appearing in the speed residual.
-/
theorem p81_2_minor_physical_bridge
    (p q s delta t : ℝ)
    (i j : Fin 4) :
    p81_2_minor p q s delta t i j =
    krylovGramCoordinate
      (krylovCenteredState
        (p81_2_state p q s delta t))
      (fun k =>
        -Complex.I *
          (p76_centeredEnergy 4
            (p81_a delta)
            (p81_b p q s)
            (p81_2_state p q s delta t)) k)
      i j := by

  unfold p81_2_minor
  rw [p81_2_centeredVelocity_eq p q s delta t]

/--
Exact algebraic decomposition.

The Krylov mean is retained.
Its contribution must not be omitted
from higher-order Taylor calculations.
-/
theorem p81_2_minor_algebra
    {n : ℕ}
    (u v : Fin n → ℂ)
    (i j : Fin n) :
    krylovGramCoordinate
      (krylovCenteredState u) v i j =
      ((i.val : ℂ) * u i * v j -
        (j.val : ℂ) * u j * v i) -
      (krylovComplexity u : ℂ) *
        (u i * v j - u j * v i) := by

  unfold krylovGramCoordinate
  unfold krylovCenteredState
  push_cast
  ring

/--
First-order product rule
for the complex Gram minor.

All derivative hypotheses concern
the component functions themselves.

No coefficient value is assumed.
-/
theorem p81_2_minor_product_rule
    (u v : ℝ → Fin 4 → ℂ)
    (du dv : Fin 4 → ℂ)
    (t : ℝ)
    (i j : Fin 4)
    (hui : HasDerivAt
      (fun x : ℝ => u x i) (du i) t)
    (huj : HasDerivAt
      (fun x : ℝ => u x j) (du j) t)
    (hvi : HasDerivAt
      (fun x : ℝ => v x i) (dv i) t)
    (hvj : HasDerivAt
      (fun x : ℝ => v x j) (dv j) t) :
    HasDerivAt
      (fun x : ℝ =>
        krylovGramCoordinate
          (u x) (v x) i j)
      (du i * v t j +
        u t i * dv j -
        (du j * v t i +
          u t j * dv i))
      t := by

  change
    HasDerivAt
      (fun x : ℝ =>
        u x i * v x j -
        u x j * v x i)
      (du i * v t j +
        u t i * dv j -
        (du j * v t i +
          u t j * dv i))
      t

  exact (hui.mul hvj).sub (huj.mul hvi)

/--
The physical velocity is the derivative
of the actual Jacobi-evolved state.

Derived from the existing P73.2 result.
-/
theorem p81_2_state_hasDerivAt
    (p q s delta t : ℝ) :
    HasDerivAt
      (p81_2_state p q s delta)
      (p81_2_velocity p q s delta t)
      t := by

  have h :=
    p73_jacobiState_hasDerivAt
      4 (p81_a delta)
      (p81_b p q s)
      t p81_e0

  change
    HasDerivAt
      (p81_2_state p q s delta)
      (((-Complex.I) •
        p81_H p q s delta).mulVec
          (p81_2_state p q s delta t))
      t at h

  have hv :
      (((-Complex.I) •
        p81_H p q s delta).mulVec
          (p81_2_state p q s delta t)) =
      p81_2_velocity p q s delta t := by

    funext j

    simp [
      p81_2_velocity,
      Matrix.mulVec,
      dotProduct,
      Finset.mul_sum,
      mul_assoc
    ]

  rw [hv] at h
  exact h

#print axioms p81_2_energyMean_zero
#print axioms p81_2_centeredVelocity_eq
#print axioms p81_2_minor_physical_bridge
#print axioms p81_2_minor_algebra
#print axioms p81_2_minor_product_rule
#print axioms p81_2_state_hasDerivAt

end Lanzarini
