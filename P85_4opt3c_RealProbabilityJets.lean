import P85_2_GeneralPhysicalObservableJets
import P85_4opt3b_RealPhaseSeparation

namespace Lanzarini

set_option maxHeartbeats 1000000
set_option maxRecDepth 1024

open scoped BigOperators

/-!
P85.4 OPT3-C

Exact phase weights.
Real polynomial probability jets.
General finite Leibniz identity.
No expected deficit coefficients.
No additional axioms.
No P79.
-/

noncomputable def p85_opt3c_phase
    (l m : ℕ) : ℝ :=
  (star ((-Complex.I) ^ l) *
    (-Complex.I) ^ m).re

theorem p85_opt3c_phase_zero :
    p85_opt3c_phase 0 0 = 1 := by
  norm_num [p85_opt3c_phase]

#print axioms p85_opt3c_phase_zero

theorem p85_opt3c_phase_period_left
    (l m : ℕ) :
    p85_opt3c_phase (l + 4) m =
      p85_opt3c_phase l m := by
  have h :
      (-Complex.I : ℂ) ^ 4 = 1 := by
    norm_num [pow_succ, Complex.I_mul_I]
  simp [p85_opt3c_phase, pow_add, h]

#print axioms p85_opt3c_phase_period_left

theorem p85_opt3c_phase_period_right
    (l m : ℕ) :
    p85_opt3c_phase l (m + 4) =
      p85_opt3c_phase l m := by
  have h :
      (-Complex.I : ℂ) ^ 4 = 1 := by
    norm_num [pow_succ, Complex.I_mul_I]
  simp [p85_opt3c_phase, pow_add, h]

#print axioms p85_opt3c_phase_period_right

theorem p85_opt3c_real_product
    (l m : ℕ)
    (x y : ℝ) :
    (star (((-Complex.I) ^ l) *
      (x : ℂ)) *
      (((-Complex.I) ^ m) *
        (y : ℂ))).re =
      p85_opt3c_phase l m * x * y := by
  simp only [p85_opt3c_phase, star_mul,
    Complex.star_def, map_mul,
    Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

#print axioms p85_opt3c_real_product

theorem p85_opt3c_physical_component
    (p q r d e f : ℝ)
    (j : Fin 4)
    (k : ℕ) :
    p85_2_z 4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0 j k 0 =
      (-Complex.I) ^ k *
        (p85_opt3b_realState
          p q r d e f k j : ℂ) := by

  have h :=
    p85_opt3b_physical_phase
      p q r d e f k

  have hj :=
    congrFun h j

  rw [p80_1_state_iteratedDeriv] at hj

  exact hj

#print axioms p85_opt3c_physical_component

noncomputable def p85_opt3c_probability
    (p q r d e f : ℝ)
    (j : Fin 4)
    (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1),
    (Nat.choose k l : ℝ) *
      p85_opt3c_phase l (k - l) *
      p85_opt3b_realState
        p q r d e f l j *
      p85_opt3b_realState
        p q r d e f (k - l) j

theorem p85_opt3c_pair_binomial
    (z w : ℕ → ℝ → ℂ)
    (k i j : ℕ)
    (t : ℝ) :
    p85_2_pairJet z w k i j t =
      ∑ l ∈ Finset.range (k + 1),
        (Nat.choose k l : ℂ) *
          (star (z (i + l) t) *
            w (j + (k - l)) t) := by
  induction k generalizing i j with
  | zero =>
      simp [p85_2_pairJet]
  | succ k ih =>
      rw [p85_2_pairJet, ih, ih]
      rw [Finset.sum_range_succ']
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      simp only [Nat.choose_zero_right,
        Nat.choose_self, Nat.cast_one,
        one_mul, Nat.add_zero,
        Nat.sub_zero, Nat.sub_self]
      -- Pascal identity and finite-sum alignment.
      simp only [Nat.choose_succ_succ,
        Nat.cast_add, add_mul]
      try rw [Finset.sum_add_distrib]
      all_goals
        try omega
      all_goals
        try ring

#print axioms p85_opt3c_pair_binomial

theorem p85_opt3c_probability_bridge
    (p q r d e f : ℝ)
    (j : Fin 4)
    (k : ℕ) :
    p85_2_probabilityJet
      4 (p84_a d e f)
      (p84_b p q r)
      p81_e0 j k 0 =
      p85_opt3c_probability
        p q r d e f j k := by

  unfold p85_2_probabilityJet
  unfold p85_opt3c_probability

  rw [p85_opt3c_pair_binomial]

  change Complex.reCLM _ = _

  rw [map_sum]

  apply Finset.sum_congr rfl

  intro l hl

  simp only [Nat.zero_add,
    p85_opt3c_physical_component,
    Complex.reCLM_apply,
    Complex.mul_re,
    Complex.natCast_re,
    Complex.natCast_im,
    zero_mul, sub_zero]

  rw [p85_opt3c_real_product]

  ring

#print axioms p85_opt3c_probability_bridge

theorem p85_opt3c_physical_probability
    (p q r d e f : ℝ)
    (j : Fin 4)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        Complex.normSq
          (jacobiState 4
            (p84_a d e f)
            (p84_b p q r)
            t p81_e0 j)) 0 =
      p85_opt3c_probability
        p q r d e f j k := by

  rw [p85_2_probability_iteratedDeriv]

  exact p85_opt3c_probability_bridge
    p q r d e f j k

#print axioms p85_opt3c_physical_probability

end Lanzarini
