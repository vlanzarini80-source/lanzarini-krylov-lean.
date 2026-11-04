
import P83_LeibnizSecond_Candidate

namespace Lanzarini

/-!
P83 auxiliary: fourth-order product formula.
The coefficient pattern follows by differentiating
an independently compiled third-order identity.
No P79 results or physical coefficient are imported.
Candidate: CI verification required.
-/

theorem p83_leibniz_fourth
    (f g : ℝ → ℂ) (x : ℝ)
    (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g)
    (hdf : Differentiable ℝ (deriv f))
    (hdg : Differentiable ℝ (deriv g))
    (hddf : Differentiable ℝ (deriv (deriv f)))
    (hddg : Differentiable ℝ (deriv (deriv g)))
    (hdddf : DifferentiableAt ℝ (deriv (deriv (deriv f))) x)
    (hdddg : DifferentiableAt ℝ (deriv (deriv (deriv g))) x) :
    deriv (deriv (deriv (deriv (fun t : ℝ => f t * g t)))) x =
      deriv (deriv (deriv (deriv f))) x * g x +
        (4 : ℂ) * deriv (deriv (deriv f)) x * deriv g x +
        (6 : ℂ) * deriv (deriv f) x * deriv (deriv g) x +
        (4 : ℂ) * deriv f x * deriv (deriv (deriv g)) x +
        f x * deriv (deriv (deriv (deriv g))) x := by

  have hthird_eq :
      deriv (deriv (deriv (fun t : ℝ => f t * g t))) =
        ((deriv (deriv (deriv f)) * g) +
          (((deriv (deriv f) * deriv g) +
              (deriv (deriv f) * deriv g)) +
            (deriv (deriv f) * deriv g))) +
        ((((deriv f * deriv (deriv g)) +
              (deriv f * deriv (deriv g))) +
            (deriv f * deriv (deriv g))) +
          (f * deriv (deriv (deriv g)))) := by
    funext y
    rw [p83_leibniz_third f g y hf hg hdf hdg (hddf y) (hddg y)]
    dsimp
    ring

  have hA : DifferentiableAt ℝ (deriv (deriv (deriv f)) * g) x :=
    hdddf.mul (hg x)
  have hB : DifferentiableAt ℝ (deriv (deriv f) * deriv g) x :=
    (hddf x).mul (hdg x)
  have hC : DifferentiableAt ℝ (deriv f * deriv (deriv g)) x :=
    (hdf x).mul (hddg x)
  have hD : DifferentiableAt ℝ (f * deriv (deriv (deriv g))) x :=
    (hf x).mul hdddg

  rw [hthird_eq]
  rw [deriv_add (hA.add ((hB.add hB).add hB))
      (((hC.add hC).add hC).add hD)]
  rw [deriv_add hA ((hB.add hB).add hB)]
  rw [deriv_add (hB.add hB) hB]
  rw [deriv_add hB hB]
  rw [deriv_add ((hC.add hC).add hC) hD]
  rw [deriv_add (hC.add hC) hC]
  rw [deriv_add hC hC]
  rw [deriv_mul hdddf (hg x)]
  rw [deriv_mul (hddf x) (hdg x)]
  rw [deriv_mul (hdf x) (hddg x)]
  rw [deriv_mul (hf x) hdddg]
  ring

#print axioms p83_leibniz_fourth

end Lanzarini
