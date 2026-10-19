
import P73_2_State
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic

/-
P74.1: Coordinate derivatives of Jacobi evolution.

The only dynamical input is the already verified
P73.2 theorem.

No coordinate differentiability hypothesis is assumed.
No physical Krylov complexity derivative is assumed.
No normalization assumption is needed.

No sorry, admit, or additional axiom.
-/

namespace Lanzarini

/--
P74.1a: Every coordinate of the evolved Jacobi state
is differentiable, with velocity supplied by P73.2.
-/
theorem p74_jacobiState_component_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (j : Fin n) :
    HasDerivAt
      (fun s : ℝ => (jacobiState n a b s psi) j)
      ((((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi)) j)
      t := by

  have hstate :=
    p73_jacobiState_hasDerivAt n a b t psi

  have hcoord :=
    (hasFDerivAt_apply
      (𝕜 := ℝ)
      j
      (jacobiState n a b t psi)).comp_hasDerivAt
        t hstate

  simpa only [
    Function.comp_def,
    ContinuousLinearMap.proj_apply
  ] using hcoord

/--
P74.1b: The real and imaginary coordinate
derivatives follow from the complex coordinate
derivative.

Both conclusions are derived, not assumed.
-/
theorem p74_jacobiState_parts_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ)
    (j : Fin n) :
    HasDerivAt
      (fun s : ℝ =>
        ((jacobiState n a b s psi) j).re)
      ((((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi)) j).re
      t
    ∧
    HasDerivAt
      (fun s : ℝ =>
        ((jacobiState n a b s psi) j).im)
      ((((-Complex.I) • jacobiComplex n a b).mulVec
        (jacobiState n a b t psi)) j).im
      t := by

  have hcoord :=
    p74_jacobiState_component_hasDerivAt
      n a b t psi j

  constructor

  · have hr :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt
        t hcoord

    simpa only [
      Function.comp_def,
      Complex.reCLM_apply
    ] using hr

  · have hi :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt
        t hcoord

    simpa only [
      Function.comp_def,
      Complex.imCLM_apply
    ] using hi

end Lanzarini

#print axioms Lanzarini.p74_jacobiState_component_hasDerivAt
#print axioms Lanzarini.p74_jacobiState_parts_hasDerivAt
