
import P78_2_PhysicalSpeedResidual
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace Lanzarini

/-!
P80.1: Exact derivatives of the physical
Jacobi evolution, at every real time.

Goal: link genuine dynamical derivatives
to powers of the Jacobi generator.

No sorry, admit, or new axioms.
Candidate requiring Lean CI verification.
-/

/--
The k-th real-time derivative of the actual
Jacobi evolution equals the k-th power of
its fixed generator acting on the evolved
state.
-/
theorem p80_1_state_iteratedDeriv
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (k : ℕ)
    (t : ℝ) :
    iteratedDeriv k
      (fun s : ℝ => jacobiState n a b s psi) t =
    (((-Complex.I) • jacobiComplex n a b) ^ k).mulVec
      (jacobiState n a b t psi) := by

  let A : Matrix (Fin n) (Fin n) ℂ :=
    (-Complex.I) • jacobiComplex n a b

  let f : ℝ → (Fin n → ℂ) :=
    fun s => jacobiState n a b s psi

  have hf (s : ℝ) :
      HasDerivAt f (A.mulVec (f s)) s := by
    exact p73_jacobiState_hasDerivAt
      n a b s psi

  have hall :
      ∀ m : ℕ, ∀ s : ℝ,
        iteratedDeriv m f s =
          (A ^ m).mulVec (f s) := by

    intro m
    induction m with
    | zero =>
        intro s
        simp

    | succ m ih =>
        intro s

        have hfun :
            iteratedDeriv m f =
              fun x : ℝ => (A ^ m).mulVec (f x) := by
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

        have hstep :
            HasDerivAt
              (fun x : ℝ =>
                (A ^ m).mulVec (f x))
              ((A ^ m).mulVec
                (A.mulVec (f s)))
              s := by
          exact LC.hasFDerivAt.comp_hasDerivAt
            s (hf s)

        calc
          iteratedDeriv (m + 1) f s =
              deriv (iteratedDeriv m f) s := by
                rw [iteratedDeriv_succ]

          _ = deriv
                (fun x : ℝ =>
                  (A ^ m).mulVec (f x)) s := by
                rw [hfun]

          _ = (A ^ m).mulVec
                (A.mulVec (f s)) :=
                hstep.deriv

          _ = (A ^ (m + 1)).mulVec (f s) := by
                rw [Matrix.mulVec_mulVec]
                rw [pow_succ]

  change
    iteratedDeriv k f t =
      (A ^ k).mulVec (f t)

  exact hall k t

/--
At time zero the k-th derivative is exactly
the k-th power of the generator applied to
the initial state.
-/
theorem p80_1_initial_derivative
    (n : ℕ)
    (a b : Fin n → ℝ)
    (psi : Fin n → ℂ)
    (k : ℕ) :
    iteratedDeriv k
      (fun t : ℝ => jacobiState n a b t psi) 0 =
    (((-Complex.I) • jacobiComplex n a b) ^ k).mulVec
      psi := by

  rw [p80_1_state_iteratedDeriv]
  rw [jacobiState_zero]

#print axioms p80_1_state_iteratedDeriv
#print axioms p80_1_initial_derivative

end Lanzarini
