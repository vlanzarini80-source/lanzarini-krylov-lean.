
import P85_2_GeneralPhysicalObservableJets
import P84_4c3_GeneralKrylovDerivative

namespace Lanzarini

/-!
P85.3 — General Physical Variance and Deficit Jets.

DOI: 10.5281/zenodo.23163367
Target: Theorem 8.1.

All six physical Jacobi parameters remain free.
Arbitrary derivative order.

No assumed cancellations.
No expected Taylor coefficients.
-/

/-- Recursive Leibniz calculus for real products. -/
noncomputable def p85_3_realPairJet
    (X Y : ℕ → ℝ → ℝ) :
    ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, i, j, t =>
      X i t * Y j t
  | k + 1, i, j, t =>
      p85_3_realPairJet X Y k (i + 1) j t +
      p85_3_realPairJet X Y k i (j + 1) t


theorem p85_3_realPairJet_hasDerivAt
    (X Y : ℕ → ℝ → ℝ)
    (hX : ∀ k t,
      HasDerivAt (X k) (X (k + 1) t) t)
    (hY : ∀ k t,
      HasDerivAt (Y k) (Y (k + 1) t) t)
    (k i j : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_3_realPairJet X Y k i j)
      (p85_3_realPairJet X Y (k + 1) i j t)
      t := by

  induction k generalizing i j with
  | zero =>
      simpa only [p85_3_realPairJet] using
        ((hX i t).mul (hY j t))

  | succ k ih =>
      simpa only [p85_3_realPairJet] using
        ((ih (i + 1) j).add
          (ih i (j + 1)))


/-- Physical Krylov moment jet. -/
noncomputable def p85_3_KJet
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  p85_2_momentJet
    4
    (p84_a d e f)
    (p84_b p q r)
    p81_e0
    (fun j : Fin 4 => (j.val : ℝ))
    k t


/-- Physical second moment jet. -/
noncomputable def p85_3_M2Jet
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  p85_2_momentJet
    4
    (p84_a d e f)
    (p84_b p q r)
    p81_e0
    (fun j : Fin 4 => (j.val : ℝ) ^ 2)
    k t


theorem p85_3_KJet_hasDerivAt
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_3_KJet p q r d e f k)
      (p85_3_KJet p q r d e f (k + 1) t)
      t := by

  exact p85_2_momentJet_hasDerivAt
    4
    (p84_a d e f)
    (p84_b p q r)
    p81_e0
    (fun j : Fin 4 => (j.val : ℝ))
    k t


theorem p85_3_M2Jet_hasDerivAt
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_3_M2Jet p q r d e f k)
      (p85_3_M2Jet p q r d e f (k + 1) t)
      t := by

  exact p85_2_momentJet_hasDerivAt
    4
    (p84_a d e f)
    (p84_b p q r)
    p81_e0
    (fun j : Fin 4 => (j.val : ℝ) ^ 2)
    k t


theorem p85_3_KJet_zero
    (p q r d e f t : ℝ) :
    p85_3_KJet p q r d e f 0 t =
      p84_4c1_K p q r d e f t := by

  simpa only [iteratedDeriv_zero,
    p85_3_KJet] using
    (p85_2_K_iteratedDeriv
      p q r d e f 0 t).symm


theorem p85_3_M2Jet_zero
    (p q r d e f t : ℝ) :
    p85_3_M2Jet p q r d e f 0 t =
      p84_4c1_M2 p q r d e f t := by

  simpa only [iteratedDeriv_zero,
    p85_3_M2Jet] using
    (p85_2_M2_iteratedDeriv
      p q r d e f 0 t).symm


/-- Krylov velocity jet, obtained by shifting
    the physical Krylov derivative order. -/
noncomputable def p85_3_JJet
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  p85_3_KJet p q r d e f (k + 1) t


theorem p85_3_JJet_hasDerivAt
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_3_JJet p q r d e f k)
      (p85_3_JJet p q r d e f (k + 1) t)
      t := by

  exact p85_3_KJet_hasDerivAt
    p q r d e f (k + 1) t


/-- Bridge to the original physical velocity. -/
theorem p85_3_JJet_zero
    (p q r d e f t : ℝ) :
    p85_3_JJet p q r d e f 0 t =
      p84_4c2_J p q r d e f t := by

  have hfun :
      p85_3_KJet p q r d e f 0 =
      p84_4c1_K p q r d e f := by

    funext s
    exact p85_3_KJet_zero
      p q r d e f s

  have h :=
    p85_3_KJet_hasDerivAt
      p q r d e f 0 t

  rw [hfun] at h

  exact h.deriv.symm.trans
    (p84_4c3_K_hasDerivAt
      p q r d e f t).deriv


/-- Physical variance jet:
    M2 minus the Leibniz jet of K squared. -/
noncomputable def p85_3_VJet
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  p85_3_M2Jet p q r d e f k t -
    p85_3_realPairJet
      (p85_3_KJet p q r d e f)
      (p85_3_KJet p q r d e f)
      k 0 0 t


theorem p85_3_VJet_hasDerivAt
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_3_VJet p q r d e f k)
      (p85_3_VJet p q r d e f (k + 1) t)
      t := by

  have hM :=
    p85_3_M2Jet_hasDerivAt
      p q r d e f k t

  have hK :=
    p85_3_realPairJet_hasDerivAt
      (p85_3_KJet p q r d e f)
      (p85_3_KJet p q r d e f)
      (p85_3_KJet_hasDerivAt p q r d e f)
      (p85_3_KJet_hasDerivAt p q r d e f)
      k 0 0 t

  exact hM.sub hK


theorem p85_3_VJet_zero
    (p q r d e f t : ℝ) :
    p85_3_VJet p q r d e f 0 t =
      p84_4c1_V p q r d e f t := by

  simp only [
    p85_3_VJet,
    p85_3_realPairJet,
    p85_3_M2Jet_zero,
    p85_3_KJet_zero,
    p84_4c1_V,
    pow_two]


/-- All physical variance derivatives. -/
theorem p85_3_V_iteratedDeriv
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (p84_4c1_V p q r d e f) t =
    p85_3_VJet p q r d e f k t := by

  have hfun :
      p84_4c1_V p q r d e f =
      p85_3_VJet p q r d e f 0 := by

    funext s
    exact
      (p85_3_VJet_zero
        p q r d e f s).symm

  rw [hfun]

  exact p85_2_tower_iteratedDeriv
    (p85_3_VJet p q r d e f)
    (p85_3_VJet_hasDerivAt p q r d e f)
    k t


/-- All physical Krylov velocity derivatives. -/
theorem p85_3_J_iteratedDeriv
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (p84_4c2_J p q r d e f) t =
    p85_3_JJet p q r d e f k t := by

  have hfun :
      p84_4c2_J p q r d e f =
      p85_3_JJet p q r d e f 0 := by

    funext s
    exact
      (p85_3_JJet_zero
        p q r d e f s).symm

  rw [hfun]

  exact p85_2_tower_iteratedDeriv
    (p85_3_JJet p q r d e f)
    (p85_3_JJet_hasDerivAt p q r d e f)
    k t


/-- Unnormalized physical speed deficit jet.

The existing repository name p84_4c2_D
corresponds to the unnormalized deficit F.
-/
noncomputable def p85_3_FJet
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) : ℝ :=
  4 * p ^ 2 *
    p85_3_VJet p q r d e f k t -
    p85_3_realPairJet
      (p85_3_JJet p q r d e f)
      (p85_3_JJet p q r d e f)
      k 0 0 t


theorem p85_3_FJet_hasDerivAt
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    HasDerivAt
      (p85_3_FJet p q r d e f k)
      (p85_3_FJet p q r d e f (k + 1) t)
      t := by

  have hV :=
    p85_3_VJet_hasDerivAt
      p q r d e f k t

  have hJ :=
    p85_3_realPairJet_hasDerivAt
      (p85_3_JJet p q r d e f)
      (p85_3_JJet p q r d e f)
      (p85_3_JJet_hasDerivAt p q r d e f)
      (p85_3_JJet_hasDerivAt p q r d e f)
      k 0 0 t

  exact
    (hV.const_mul (4 * p ^ 2)).sub hJ


theorem p85_3_FJet_zero
    (p q r d e f t : ℝ) :
    p85_3_FJet p q r d e f 0 t =
      p84_4c2_D p q r d e f t := by

  simp only [
    p85_3_FJet,
    p85_3_realPairJet,
    p85_3_VJet_zero,
    p85_3_JJet_zero,
    p84_4c2_D,
    pow_two]


/-- Main physical deficit derivative theorem.
    Valid for every derivative order. -/
theorem p85_3_F_iteratedDeriv
    (p q r d e f : ℝ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (p84_4c2_D p q r d e f) t =
    p85_3_FJet p q r d e f k t := by

  have hfun :
      p84_4c2_D p q r d e f =
      p85_3_FJet p q r d e f 0 := by

    funext s
    exact
      (p85_3_FJet_zero
        p q r d e f s).symm

  rw [hfun]

  exact p85_2_tower_iteratedDeriv
    (p85_3_FJet p q r d e f)
    (p85_3_FJet_hasDerivAt p q r d e f)
    k t


/-- Initial physical deficit jet at arbitrary order. -/
theorem p85_3_F_initialJet
    (p q r d e f : ℝ)
    (k : ℕ) :
    iteratedDeriv k
      (p84_4c2_D p q r d e f) 0 =
    p85_3_FJet p q r d e f k 0 := by

  exact p85_3_F_iteratedDeriv
    p q r d e f k 0


/-- DOI base-case specialization.
    No coefficient is assumed or inserted. -/
theorem p85_3_DOI_base_initialJet
    (p q r delta : ℝ)
    (k : ℕ) :
    iteratedDeriv k
      (p84_4c2_D p q r 0 0 delta) 0 =
    p85_3_FJet p q r 0 0 delta k 0 := by

  exact p85_3_F_initialJet
    p q r 0 0 delta k


#print axioms p85_3_realPairJet_hasDerivAt
#print axioms p85_3_KJet_hasDerivAt
#print axioms p85_3_M2Jet_hasDerivAt
#print axioms p85_3_KJet_zero
#print axioms p85_3_M2Jet_zero
#print axioms p85_3_JJet_hasDerivAt
#print axioms p85_3_JJet_zero
#print axioms p85_3_VJet_hasDerivAt
#print axioms p85_3_VJet_zero
#print axioms p85_3_V_iteratedDeriv
#print axioms p85_3_J_iteratedDeriv
#print axioms p85_3_FJet_hasDerivAt
#print axioms p85_3_FJet_zero
#print axioms p85_3_F_iteratedDeriv
#print axioms p85_3_F_initialJet
#print axioms p85_3_DOI_base_initialJet

end Lanzarini
