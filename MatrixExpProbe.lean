
import Mathlib
import JacobiEvolution

namespace Lanzarini

/--
Propagatore quantistico:
U(t) = exp(-i t H).
-/
noncomputable def jacobiPropagator
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp ℂ
    (jacobiEvolutionGenerator n a b t)

/--
Generatore nullo al tempo zero.
-/
theorem jacobiEvolutionGenerator_zero
    (n : ℕ) (a b : Fin n → ℝ) :
    jacobiEvolutionGenerator n a b 0 = 0 := by
  simp [jacobiEvolutionGenerator]

/--
Propagatore identita' al tempo zero.
-/
theorem jacobiPropagator_zero
    (n : ℕ) (a b : Fin n → ℝ) :
    jacobiPropagator n a b 0 = 1 := by
  rw [jacobiPropagator]
  rw [jacobiEvolutionGenerator_zero]
  exact NormedSpace.exp_zero

/--
P52: unitarieta' del propagatore.
-/
theorem jacobiPropagator_unitary
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ) :
    (jacobiPropagator n a b t).conjTranspose *
      jacobiPropagator n a b t = 1 := by
  let G := jacobiEvolutionGenerator n a b t

  have hG : G.conjTranspose = -G := by
    exact jacobiEvolutionGenerator_conjTranspose n a b t

  change (NormedSpace.exp ℂ G).conjTranspose *
    NormedSpace.exp ℂ G = 1

  rw [← Matrix.exp_conjTranspose]
  rw [hG]

  have hc : Commute (-G) G := by
    exact (Commute.refl G).neg_left

  rw [← Matrix.exp_add_of_commute ℂ (-G) G hc]
  simp

/--
P53: stato quantistico evoluto.
-/
noncomputable def jacobiState
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    Fin n → ℂ :=
  (jacobiPropagator n a b t).mulVec psi

/--
Prodotto interno complesso.
-/
noncomputable def jacobiInner
    {n : ℕ} (v w : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, star (v j) * w j

/--
Norma quadratica reale.
-/
noncomputable def jacobiNormSq
    {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  ∑ j : Fin n, Complex.normSq (v j)

/--
Lo stato al tempo zero coincide
con lo stato iniziale.
-/
theorem jacobiState_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    jacobiState n a b 0 psi = psi := by
  unfold jacobiState
  rw [jacobiPropagator_zero]
  simp

/--
P53.1: norma quadratica al tempo zero.
-/
theorem jacobiNormSq_state_zero
    (n : ℕ) (a b : Fin n → ℝ)
    (psi : Fin n → ℂ) :
    jacobiNormSq (jacobiState n a b 0 psi) =
      jacobiNormSq psi := by
  rw [jacobiState_zero]

/--
P53.2: prodotto interno e norma quadratica.
-/
theorem jacobiInner_self
    {n : ℕ} (v : Fin n → ℂ) :
    jacobiInner v v =
      (jacobiNormSq v : ℂ) := by
  unfold jacobiInner jacobiNormSq
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa using
    (Complex.normSq_eq_conj_mul_self
      (z := v j)).symm

/--
P53.3a: l'evoluzione unitaria conserva
il prodotto interno di uno stato
con se stesso, per ogni tempo reale.
-/
theorem jacobiInner_state_self
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    jacobiInner (jacobiState n a b t psi)
      (jacobiState n a b t psi) =
        jacobiInner psi psi := by
  unfold jacobiState
  let U := jacobiPropagator n a b t
  change star (U *ᵥ psi) ⬝ᵥ (U *ᵥ psi) =
    star psi ⬝ᵥ psi
  rw [Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec]
  rw [← Matrix.mulVec_mulVec]
  have hU : U.conjTranspose * U = 1 := by
    exact jacobiPropagator_unitary n a b t
  rw [hU]
  rw [Matrix.one_mulVec]

/--
P53.3b: conservazione della norma
quadratica per ogni tempo reale.

Non richiede che lo stato iniziale
sia normalizzato.
-/
theorem jacobiNormSq_state
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    jacobiNormSq (jacobiState n a b t psi) =
      jacobiNormSq psi := by
  have h :=
    jacobiInner_state_self n a b t psi
  rw [jacobiInner_self, jacobiInner_self] at h
  exact Complex.ofReal_injective h

end Lanzarini
