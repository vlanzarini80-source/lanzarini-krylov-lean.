
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

namespace Lanzarini

/-!
P83 auxiliary: second derivative of a product.

Independent of P79 and P83.4b.
Lean 4.24.0 / mathlib v4.24.0 candidate.

No new axioms.
No sorry.
Not yet CI verified.
-/

theorem p83_leibniz_second
    (f g : ℝ → ℂ) (x : ℝ)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y)
    (hfx : DifferentiableAt ℝ f x)
    (hgx : DifferentiableAt ℝ g x)
    (hdf : DifferentiableAt ℝ (deriv f) x)
    (hdg : DifferentiableAt ℝ (deriv g) x) :
    deriv (deriv (fun t : ℝ => f t * g t)) x =
      deriv (deriv f) x * g x +
        (2 : ℂ) * deriv f x * deriv g x +
        f x * deriv (deriv g) x := by

  have hlocal :
      deriv (fun t : ℝ => f t * g t) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          deriv f y * g y +
            f y * deriv g y) := by
    filter_upwards [hf, hg] with y hfy hgy
    exact deriv_fun_mul hfy hgy

  rw [Filter.EventuallyEq.deriv_eq hlocal]
  rw [deriv_fun_add (hdf.mul hgx) (hfx.mul hdg)]
  rw [deriv_fun_mul hdf hgx]
  rw [deriv_fun_mul hfx hdg]
  ring

#print axioms p83_leibniz_second

end Lanzarini
