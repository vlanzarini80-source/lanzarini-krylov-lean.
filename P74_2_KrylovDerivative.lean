
import P74_1_Components
import KrylovGap

/-
P74.2: Physical Krylov complexity derivative
along finite-dimensional Jacobi evolution.

Uses the verified results:
P72.2: Componentwise Krylov differentiation.
P74.1: Real and imaginary state derivatives.

No differentiability hypothesis is assumed.
No normalization hypothesis is required.
No desired conclusion is assumed.

No sorry, admit, or new axiom.
-/

namespace Lanzarini

/--
P74.2: The physical Krylov complexity derivative
is obtained by applying P72.2 to the Jacobi state,
using the coordinate derivatives proved in P74.1.
-/
theorem p74_krylovComplexityAt_hasDerivAt
    (n : ℕ) (a b : Fin n → ℝ)
    (t : ℝ) (psi : Fin n → ℂ) :
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexityAt n a b s psi)
      (2 * (∑ j : Fin n,
        (j.val : ℝ) *
          (star ((jacobiState n a b t psi) j) *
            ((((-Complex.I) • jacobiComplex n a b).mulVec
              (jacobiState n a b t psi)) j)).re))
      t := by

  -- Physical velocity derived in P73.2.
  let velocity : Fin n → ℂ :=
    ((-Complex.I) • jacobiComplex n a b).mulVec
      (jacobiState n a b t psi)

  -- P74.1 supplies both component derivatives.
  have hparts (j : Fin n) :=
    p74_jacobiState_parts_hasDerivAt
      n a b t psi j

  -- Apply the already verified P72.2 theorem.
  have hK :=
    krylovComplexity_hasDerivAt_components
      (fun s : ℝ => jacobiState n a b s psi)
      velocity
      t
      (fun j => (hparts j).1)
      (fun j => (hparts j).2)

  -- Unfold only the definition of physical
  -- Krylov complexity and the local velocity.
  change
    HasDerivAt
      (fun s : ℝ =>
        krylovComplexity
          (jacobiState n a b s psi))
      (2 * (∑ j : Fin n,
        (j.val : ℝ) *
          (star ((jacobiState n a b t psi) j) *
            velocity j).re))
      t

  exact hK

end Lanzarini

#print axioms Lanzarini.p74_krylovComplexityAt_hasDerivAt
