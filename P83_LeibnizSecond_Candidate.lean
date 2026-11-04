
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

namespace Lanzarini

/-!
P83 auxiliary Leibniz identities.

Second order: previously verified by isolated CI #4.
Third order: new candidate requiring CI.

No imported P79 coefficients.
No additional axioms.
No sorry.
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

  change
    deriv
      ((deriv f * g) + (f * deriv g)) x =
      deriv (deriv f) x * g x +
        (2 : ℂ) * deriv f x * deriv g x +
        f x * deriv (deriv g) x

  rw [deriv_add (hdf.mul hgx) (hfx.mul hdg)]
  rw [deriv_mul hdf hgx]
  rw [deriv_mul hfx hdg]
  ring

#print axioms p83_leibniz_second

/--
Third derivative of a product.

This auxiliary statement uses global
differentiability of lower derivatives.
It does not modify P83.4b.
-/
theorem p83_leibniz_third
    (f g : ℝ → ℂ) (x : ℝ)
    (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g)
    (hdf : Differentiable ℝ (deriv f))
    (hdg : Differentiable ℝ (deriv g))
    (hddf :
      DifferentiableAt ℝ (deriv (deriv f)) x)
    (hddg :
      DifferentiableAt ℝ (deriv (deriv g)) x) :
    deriv (deriv (deriv
      (fun t : ℝ => f t * g t))) x =
      deriv (deriv (deriv f)) x * g x +
        (3 : ℂ) *
          deriv (deriv f) x * deriv g x +
        (3 : ℂ) *
          deriv f x * deriv (deriv g) x +
        f x * deriv (deriv (deriv g)) x := by

  have hsecond_eq :
      deriv (deriv
        (fun t : ℝ => f t * g t)) =
        ((deriv (deriv f) * g) +
          (deriv f * deriv g)) +
        ((deriv f * deriv g) +
          (f * deriv (deriv g))) := by
    funext y
    rw [p83_leibniz_second f g y
      (Filter.Eventually.of_forall
        (fun z => hf z))
      (Filter.Eventually.of_forall
        (fun z => hg z))
      (hf y) (hg y) (hdf y) (hdg y)]
    dsimp
    ring

  rw [hsecond_eq]

  rw [deriv_add
    ((hddf.mul (hg x)).add
      ((hdf x).mul (hdg x)))
    (((hdf x).mul (hdg x)).add
      ((hf x).mul hddg))]

  rw [deriv_add
    (hddf.mul (hg x))
    ((hdf x).mul (hdg x))]

  rw [deriv_add
    ((hdf x).mul (hdg x))
    ((hf x).mul hddg)]

  rw [deriv_mul hddf (hg x)]
  rw [deriv_mul (hdf x) (hdg x)]
  rw [deriv_mul (hf x) hddg]

  ring

#print axioms p83_leibniz_third

end Lanzarini
