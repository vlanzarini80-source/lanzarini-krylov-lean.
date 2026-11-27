
import P80_1_TrueEvolutionJets
import P84_4r7a_PhysicalVelocitySecondDerivative

namespace Lanzarini

/-!
P85.1 — General Physical Jet Closure.

DOI: 10.5281/zenodo.23163367
Target: Theorem 8.1.

Arbitrary finite dimension.
Arbitrary derivative order.
Actual physical Jacobi evolution.
-/

theorem p85_1_projection_hasDerivAt
    (n : ℕ)
    (j : Fin n)
    (f : ℝ → Fin n → ℂ)
    (df : Fin n → ℂ)
    (t : ℝ)
    (hf : HasDerivAt f df t) :
    HasDerivAt
      (fun s : ℝ => f s j)
      (df j)
      t := by

  let L : (Fin n → ℂ) →ₗ[ℝ] ℂ :=
    {
      toFun := fun v => v j
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl
    }

  let LC : (Fin n → ℂ) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap L

  exact LC.hasFDerivAt.comp_hasDerivAt t hf


theorem p85_1_component_iteratedDeriv
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (fun s : ℝ =>
        jacobiState n a b s psi j) t =
    ((((-Complex.I) •
      jacobiComplex n a b) ^ k).mulVec
        (jacobiState n a b t psi)) j := by

  let A : Matrix (Fin n) (Fin n) ℂ :=
    (-Complex.I) • jacobiComplex n a b

  let f : ℝ → Fin n → ℂ :=
    fun s => jacobiState n a b s psi

  have hf (s : ℝ) :
      HasDerivAt f (A.mulVec (f s)) s := by
    exact p73_jacobiState_hasDerivAt
      n a b s psi

  have hall :
      ∀ m : ℕ, ∀ s : ℝ,
        iteratedDeriv m
          (fun x : ℝ => f x j) s =
        ((A ^ m).mulVec (f s)) j := by

    intro m

    induction m with
    | zero =>
        intro s
        simp

    | succ m ih =>
        intro s

        have hfun :
            iteratedDeriv m
              (fun x : ℝ => f x j) =
            (fun x : ℝ =>
              ((A ^ m).mulVec (f x)) j) := by
          funext x
          exact ih x

        let L :
            (Fin n → ℂ) →ₗ[ℝ]
              (Fin n → ℂ) :=
          (Matrix.mulVecBilin ℝ ℝ) (A ^ m)

        let LC :
            (Fin n → ℂ) →L[ℝ]
              (Fin n → ℂ) :=
          LinearMap.toContinuousLinearMap L

        have hv :
            HasDerivAt
              (fun x : ℝ =>
                (A ^ m).mulVec (f x))
              ((A ^ m).mulVec
                (A.mulVec (f s))) s := by

          exact LC.hasFDerivAt.comp_hasDerivAt
            s (hf s)

        have hj :=
          p85_1_projection_hasDerivAt
            n j
            (fun x : ℝ =>
              (A ^ m).mulVec (f x))
            ((A ^ m).mulVec
              (A.mulVec (f s)))
            s hv

        calc
          iteratedDeriv (m + 1)
              (fun x : ℝ => f x j) s =
            deriv
              (iteratedDeriv m
                (fun x : ℝ => f x j)) s := by
                  rw [iteratedDeriv_succ]

          _ = deriv
              (fun x : ℝ =>
                ((A ^ m).mulVec (f x)) j) s := by
                  rw [hfun]

          _ = ((A ^ m).mulVec
                (A.mulVec (f s))) j :=
                  hj.deriv

          _ = ((A ^ (m + 1)).mulVec
                (f s)) j := by
                  rw [Matrix.mulVec_mulVec]
                  rw [pow_succ]

  exact hall k t


theorem p85_1_component_initial_jet
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (j : Fin n)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        jacobiState n a b t psi j) 0 =
    ((((-Complex.I) •
      jacobiComplex n a b) ^ k).mulVec
        psi) j := by

  rw [p85_1_component_iteratedDeriv]
  rw [jacobiState_zero]


theorem p85_1_four_site_initial_jet
    (p q r d e f : ℝ)
    (j : Fin 4)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ =>
        p84_4l_psi p q r d e f t j) 0 =
    ((((-Complex.I) •
      jacobiComplex 4
        (p84_a d e f)
        (p84_b p q r)) ^ k).mulVec
          p81_e0) j := by

  simpa only [p84_4l_psi] using
    (p85_1_component_initial_jet
      4
      (p84_a d e f)
      (p84_b p q r)
      p81_e0 j k)


#print axioms p85_1_projection_hasDerivAt
#print axioms p85_1_component_iteratedDeriv
#print axioms p85_1_component_initial_jet
#print axioms p85_1_four_site_initial_jet

end Lanzarini
