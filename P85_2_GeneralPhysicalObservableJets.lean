
import P85_1_GeneralPhysicalJetClosure
import Mathlib

namespace Lanzarini

/-!
P85.2 — General Physical Observable Jets.

DOI: 10.5281/zenodo.23163367
Target: Theorem 8.1.

Recursive Leibniz calculus.
Arbitrary derivative order.
Arbitrary finite dimension.
-/

/-- Physical component jet. -/
noncomputable def p85_2_z
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ)
    (t : ℝ) : ℂ :=
  ((((-Complex.I) •
    jacobiComplex n a b) ^ k).mulVec
      (jacobiState n a b t psi)) j


/-- Every physical jet differentiates
    to the next physical jet. -/
theorem p85_2_z_hasDerivAt
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_2_z n a b psi j k)
      (p85_2_z n a b psi j (k + 1) t)
      t := by

  let A : Matrix (Fin n) (Fin n) ℂ :=
    (-Complex.I) • jacobiComplex n a b

  let f : ℝ → Fin n → ℂ :=
    fun s => jacobiState n a b s psi

  let L :
      (Fin n → ℂ) →ₗ[ℝ]
        (Fin n → ℂ) :=
    (Matrix.mulVecBilin ℝ ℝ) (A ^ k)

  let LC :
      (Fin n → ℂ) →L[ℝ]
        (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap L

  have hf :
      HasDerivAt f (A.mulVec (f t)) t := by
    exact p73_jacobiState_hasDerivAt
      n a b t psi

  have hv :
      HasDerivAt
        (fun s : ℝ =>
          (A ^ k).mulVec (f s))
        ((A ^ k).mulVec
          (A.mulVec (f t))) t := by

    exact LC.hasFDerivAt.comp_hasDerivAt
      t hf

  have hj :=
    p85_1_projection_hasDerivAt
      n j
      (fun s : ℝ =>
        (A ^ k).mulVec (f s))
      ((A ^ k).mulVec
        (A.mulVec (f t)))
      t hv

  change
    HasDerivAt
      (fun s : ℝ =>
        ((A ^ k).mulVec (f s)) j)
      ((A ^ (k + 1)).mulVec (f t)) j
      t

  rw [pow_succ, ← Matrix.mulVec_mulVec]

  exact hj


/-- Recursive Leibniz jet of a
    conjugated product. -/
noncomputable def p85_2_pairJet
    (z w : ℕ → ℝ → ℂ) :
    ℕ → ℕ → ℕ → ℝ → ℂ
  | 0, i, j, t =>
      star (z i t) * w j t
  | k + 1, i, j, t =>
      p85_2_pairJet z w k (i + 1) j t +
      p85_2_pairJet z w k i (j + 1) t


/-- Recursive Leibniz rule. -/
theorem p85_2_pairJet_hasDerivAt
    (z w : ℕ → ℝ → ℂ)
    (hz : ∀ k t,
      HasDerivAt (z k) (z (k + 1) t) t)
    (hw : ∀ k t,
      HasDerivAt (w k) (w (k + 1) t) t)
    (k i j : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_2_pairJet z w k i j)
      (p85_2_pairJet z w (k + 1) i j t)
      t := by

  induction k generalizing i j with
  | zero =>
      simpa only [p85_2_pairJet] using
        ((hz i t).star.mul (hw j t))

  | succ k ih =>
      simpa only [p85_2_pairJet] using
        ((ih (i + 1) j).add
          (ih i (j + 1)))


/-- Real physical probability jet. -/
noncomputable def p85_2_probabilityJet
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  (p85_2_pairJet
    (p85_2_z n a b psi j)
    (p85_2_z n a b psi j)
    k 0 0 t).re


theorem p85_2_probabilityJet_hasDerivAt
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_2_probabilityJet
        n a b psi j k)
      (p85_2_probabilityJet
        n a b psi j (k + 1) t)
      t := by

  have h :=
    p85_2_pairJet_hasDerivAt
      (p85_2_z n a b psi j)
      (p85_2_z n a b psi j)
      (p85_2_z_hasDerivAt n a b psi j)
      (p85_2_z_hasDerivAt n a b psi j)
      k 0 0 t

  exact
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt
      t h


theorem p85_2_probabilityJet_zero
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (t : ℝ) :
    p85_2_probabilityJet
      n a b psi j 0 t =
    Complex.normSq
      (jacobiState n a b t psi j) := by

  simp [p85_2_probabilityJet,
    p85_2_pairJet, p85_2_z,
    Complex.normSq, Complex.mul_re]
  <;> ring


/-- Weighted physical observable jet.
    The weights are arbitrary real numbers. -/
noncomputable def p85_2_momentJet
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (weight : Fin n → ℝ)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  ∑ j : Fin n,
    weight j *
      p85_2_probabilityJet
        n a b psi j k t


theorem p85_2_momentJet_hasDerivAt
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (weight : Fin n → ℝ)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_2_momentJet
        n a b psi weight k)
      (p85_2_momentJet
        n a b psi weight (k + 1) t)
      t := by

  unfold p85_2_momentJet

  apply HasDerivAt.fun_sum

  intro j hj

  exact
    (p85_2_probabilityJet_hasDerivAt
      n a b psi j k t).const_mul
        (weight j)


/-- General derivative tower. -/
theorem p85_2_tower_iteratedDeriv
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ k t,
      HasDerivAt (F k) (F (k + 1) t) t)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k (F 0) t = F k t := by

  induction k generalizing t with
  | zero =>
      simp

  | succ k ih =>
      have hfun :
          iteratedDeriv k (F 0) = F k := by
        funext s
        exact ih s

      rw [iteratedDeriv_succ, hfun]

      exact (hF k t).deriv


theorem p85_2_probability_iteratedDeriv
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (fun s : ℝ =>
        Complex.normSq
          (jacobiState n a b s psi j)) t =
    p85_2_probabilityJet
      n a b psi j k t := by

  have hfun :
      (fun s : ℝ =>
        Complex.normSq
          (jacobiState n a b s psi j)) =
      p85_2_probabilityJet
        n a b psi j 0 := by

    funext s

    exact
      (p85_2_probabilityJet_zero
        n a b psi j s).symm

  rw [hfun]

  exact
    p85_2_tower_iteratedDeriv
      (p85_2_probabilityJet n a b psi j)
      (p85_2_probabilityJet_hasDerivAt
        n a b psi j)
      k t


theorem p85_2_moment_iteratedDeriv
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (weight : Fin n → ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (fun s : ℝ =>
        ∑ j : Fin n,
          weight j *
            Complex.normSq
              (jacobiState n a b s psi j))
      t =
    p85_2_momentJet
      n a b psi weight k t := by

  have hfun :
      (fun s : ℝ =>
        ∑ j : Fin n,
          weight j *
            Complex.normSq
              (jacobiState n a b s psi j)) =
      p85_2_momentJet
        n a b psi weight 0 := by

    funext s

    simp only [p85_2_momentJet,
      p85_2_probabilityJet_zero]

  rw [hfun]

  exact
    p85_2_tower_iteratedDeriv
      (p85_2_momentJet n a b psi weight)
      (p85_2_momentJet_hasDerivAt
        n a b psi weight)
      k t


/-- Physical Krylov complexity:
    all derivative orders. -/
theorem p85_2_K_iteratedDeriv
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (p84_4c1_K p q r d e f) t =
    p85_2_momentJet
      4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0
      (fun j : Fin 4 => (j.val : ℝ))
      k t := by

  simpa only [p84_4c1_K,
    p84_4c1_state] using
    (p85_2_moment_iteratedDeriv
      4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0
      (fun j : Fin 4 => (j.val : ℝ))
      k t)


/-- Physical second moment:
    all derivative orders. -/
theorem p85_2_M2_iteratedDeriv
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (p84_4c1_M2 p q r d e f) t =
    p85_2_momentJet
      4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0
      (fun j : Fin 4 => (j.val : ℝ) ^ 2)
      k t := by

  simpa only [p84_4c1_M2,
    p84_4c1_state] using
    (p85_2_moment_iteratedDeriv
      4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0
      (fun j : Fin 4 => (j.val : ℝ) ^ 2)
      k t)


#print axioms p85_2_z_hasDerivAt
#print axioms p85_2_pairJet_hasDerivAt
#print axioms p85_2_probabilityJet_hasDerivAt
#print axioms p85_2_probabilityJet_zero
#print axioms p85_2_momentJet_hasDerivAt
#print axioms p85_2_tower_iteratedDeriv
#print axioms p85_2_probability_iteratedDeriv
#print axioms p85_2_moment_iteratedDeriv
#print axioms p85_2_K_iteratedDeriv
#print axioms p85_2_M2_iteratedDeriv

end Lanzarini
