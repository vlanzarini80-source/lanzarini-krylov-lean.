import P81_2a_PhysicalGramBridge

namespace Lanzarini

/-!
P81.2b.0 - Initial physical data.
Candidate requiring Lean CI compilation.
No target coefficients assumed.
-/

theorem p81_2b_state_zero (p q s delta : ℝ) :
    p81_2_state p q s delta 0 = p81_e0 := by
  unfold p81_2_state
  exact jacobiState_zero 4 (p81_a delta) (p81_b p q s) p81_e0

theorem p81_2b_initial_krylov_zero :
    krylovComplexity p81_e0 = 0 := by
  simp [krylovComplexity, p81_e0, Fin.sum_univ_succ]

theorem p81_2b_centered_state_zero (p q s delta : ℝ) :
    krylovCenteredState (p81_2_state p q s delta 0) = 0 := by
  rw [p81_2b_state_zero]
  funext j
  fin_cases j <;>
    simp [krylovCenteredState, p81_e0, p81_2b_initial_krylov_zero]

theorem p81_2b_velocity_at_zero (p q s delta : ℝ) :
    p81_2_velocity p q s delta 0 =
      ![0, -Complex.I * (p : ℂ), 0, 0] := by
  funext j
  fin_cases j <;>
    simp [p81_2_velocity, p81_2b_state_zero, p81_H1]

theorem p81_2b_state_initial_derivative (p q s delta : ℝ) :
    HasDerivAt (p81_2_state p q s delta)
      ![0, -Complex.I * (p : ℂ), 0, 0] 0 := by
  have h := p81_2_state_hasDerivAt p q s delta 0
  rw [p81_2b_velocity_at_zero] at h
  exact h

theorem p81_2b_minor_zero (p q s delta : ℝ) (i j : Fin 4) :
    p81_2_minor p q s delta 0 i j = 0 := by
  unfold p81_2_minor
  rw [p81_2b_centered_state_zero]
  simp [krylovGramCoordinate]

theorem p81_2b_krylov_initial_hasDerivAt (p q s delta : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        krylovComplexityAt 4 (p81_a delta)
          (p81_b p q s) t p81_e0)
      0 0 := by
  have hn : jacobiNormSq p81_e0 = 1 := by
    simp [jacobiNormSq, p81_e0, Fin.sum_univ_succ]
  have h := p75_centered_derivative 4
    (p81_a delta) (p81_b p q s) 0 p81_e0 hn
  rw [jacobiState_zero] at h
  have hc : krylovCenteredState p81_e0 = 0 := by
    simpa only [p81_2b_state_zero] using
      (p81_2b_centered_state_zero p q s delta)
  rw [hc] at h
  simpa [jacobiInner] using h

theorem p81_2b_speedChannel_zero (p q s delta : ℝ) :
    p78_speedChannelAt 4 (p81_a delta)
      (p81_b p q s) 0 p81_e0 = 0 := by
  unfold p78_speedChannelAt
  rw [jacobiState_zero]
  have hc : krylovCenteredState p81_e0 = 0 := by
    simpa only [p81_2b_state_zero] using
      (p81_2b_centered_state_zero p q s delta)
  rw [hc]
  simp [jacobiInner]

#print axioms p81_2b_state_zero
#print axioms p81_2b_initial_krylov_zero
#print axioms p81_2b_centered_state_zero
#print axioms p81_2b_velocity_at_zero
#print axioms p81_2b_state_initial_derivative
#print axioms p81_2b_minor_zero
#print axioms p81_2b_krylov_initial_hasDerivAt
#print axioms p81_2b_speedChannel_zero

end Lanzarini
