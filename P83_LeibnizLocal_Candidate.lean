
import P83_LeibnizSecond_Candidate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

namespace Lanzarini

/-!
P83 local Leibniz bridge.

Stage 1:
Local differentiability of iterated derivatives.

No P79.
No physical coefficients.
No sorry or admit.
No additional axioms.

Candidate requiring actual Lean compilation.
-/

private theorem p83_local_diff_iterated
    (f : ℝ → ℂ)
    (x : ℝ)
    (m : ℕ)
    (hf : ContDiffAt ℝ 4 f x)
    (hm : m < 4) :
    DifferentiableAt ℝ
      (iteratedDeriv m f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact
    (ContinuousMultilinearMap.piFieldEquiv
      ℝ (Fin m) ℂ).symm.differentiableAt.comp x
      (hf.differentiableAt_iteratedFDeriv
        (by exact_mod_cast hm))

private theorem p83_local_eventually_diff
    (f : ℝ → ℂ)
    (x : ℝ)
    (m : ℕ)
    (hf : ContDiffAt ℝ 4 f x)
    (hm : m < 4) :
    ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ
        (iteratedDeriv m f) y := by
  filter_upwards
    [hf.eventually (by simp)] with y hy
  exact p83_local_diff_iterated
    f y m hy hm

end Lanzarini
