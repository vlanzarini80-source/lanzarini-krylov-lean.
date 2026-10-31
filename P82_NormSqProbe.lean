
import Mathlib

namespace Lanzarini

theorem p82_normSq_probe
    (f : ℝ → ℂ) (t : ℝ) (dz : ℂ)
    (hre : HasDerivAt
      (fun x : ℝ => (f x).re) dz.re t)
    (him : HasDerivAt
      (fun x : ℝ => (f x).im) dz.im t) :
    HasDerivAt
      (fun x : ℝ => Complex.normSq (f x))
      (2 * ((star (f t)) * dz).re) t := by

  have h := (hre.pow 2).add (him.pow 2)

  have hfun :
      (fun x : ℝ => Complex.normSq (f x)) =
      ((fun x : ℝ => (f x).re) ^ 2 +
       (fun x : ℝ => (f x).im) ^ 2) := by
    funext x
    simp only [Complex.normSq_apply]
    change
      (f x).re * (f x).re +
        (f x).im * (f x).im =
      (f x).re ^ 2 + (f x).im ^ 2
    ring

  have hderiv :
      2 * ((star (f t)) * dz).re =
      2 * (f t).re * dz.re +
        2 * (f t).im * dz.im := by
    simp only [Complex.mul_re]
    change
      2 * ((f t).re * dz.re -
        (-(f t).im) * dz.im) =
      2 * (f t).re * dz.re +
        2 * (f t).im * dz.im
    ring

  rw [hfun, hderiv]
  convert h using 1 <;> ring

#print axioms p82_normSq_probe

end Lanzarini
