
import P83_LeibnizLocal_Candidate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

namespace Lanzarini

/-!
P83: local fourth-order product cancellation.

Derived from the local third-order Leibniz
identity and fourth-order regularity.

No P79.
No assumed physical coefficients.
No new axioms.
-/

private theorem p83_fourth_diff_iterated
    (f : ℝ → ℂ)
    (m : ℕ)
    (hf : ContDiffAt ℝ 4 f 0)
    (hm : m < 4) :
    DifferentiableAt ℝ
      (iteratedDeriv m f) 0 := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact
    (ContinuousMultilinearMap.piFieldEquiv
      ℝ (Fin m) ℂ).symm.differentiableAt.comp 0
      (hf.differentiableAt_iteratedFDeriv
        (by exact_mod_cast hm))

theorem p83_local_fourth_product_zero
    (f g : ℝ → ℂ)
    (hf : ContDiffAt ℝ 4 f 0)
    (hg : ContDiffAt ℝ 4 g 0)
    (hf0 : iteratedDeriv 0 f 0 = 0)
    (hf1 : iteratedDeriv 1 f 0 = 0)
    (hg0 : iteratedDeriv 0 g 0 = 0)
    (hg1 : iteratedDeriv 1 g 0 = 0)
    (hg2 : iteratedDeriv 2 g 0 = 0) :
    iteratedDeriv 4
      (fun t : ℝ => f t * g t) 0 = 0 := by

  have f0 : f 0 = 0 := by
    simpa only [iteratedDeriv_zero] using hf0

  have f1 : deriv f 0 = 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using hf1

  have g0 : g 0 = 0 := by
    simpa only [iteratedDeriv_zero] using hg0

  have g1 : deriv g 0 = 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using hg1

  have g2 : deriv (deriv g) 0 = 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using hg2

  have df0 : DifferentiableAt ℝ f 0 := by
    simpa only [iteratedDeriv_zero] using
      p83_fourth_diff_iterated f 0 hf (by omega)

  have df1 :
      DifferentiableAt ℝ (deriv f) 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using p83_fourth_diff_iterated
        f 1 hf (by omega)

  have df2 :
      DifferentiableAt ℝ
        (deriv (deriv f)) 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using p83_fourth_diff_iterated
        f 2 hf (by omega)

  have df3 :
      DifferentiableAt ℝ
        (deriv (deriv (deriv f))) 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using p83_fourth_diff_iterated
        f 3 hf (by omega)

  have dg0 : DifferentiableAt ℝ g 0 := by
    simpa only [iteratedDeriv_zero] using
      p83_fourth_diff_iterated g 0 hg (by omega)

  have dg1 :
      DifferentiableAt ℝ (deriv g) 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using p83_fourth_diff_iterated
        g 1 hg (by omega)

  have dg2 :
      DifferentiableAt ℝ
        (deriv (deriv g)) 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using p83_fourth_diff_iterated
        g 2 hg (by omega)

  have dg3 :
      DifferentiableAt ℝ
        (deriv (deriv (deriv g))) 0 := by
    simpa only
      [iteratedDeriv_succ, iteratedDeriv_zero]
      using p83_fourth_diff_iterated
        g 3 hg (by omega)

  have hA :
      HasDerivAt
        (fun t : ℝ =>
          deriv (deriv (deriv f)) t * g t)
        0 0 := by
    convert df3.hasDerivAt.mul dg0.hasDerivAt
      using 1 <;> simp [g0, g1]

  have hB :
      HasDerivAt
        (fun t : ℝ =>
          (3 : ℂ) *
            (deriv (deriv f) t * deriv g t))
        0 0 := by
    have h :=
      (df2.hasDerivAt.mul dg1.hasDerivAt).const_mul
        (3 : ℂ)
    simpa [g1, g2] using h

  have hC :
      HasDerivAt
        (fun t : ℝ =>
          (3 : ℂ) *
            (deriv f t * deriv (deriv g) t))
        0 0 := by
    have h :=
      (df1.hasDerivAt.mul dg2.hasDerivAt).const_mul
        (3 : ℂ)
    simpa [f1, g2] using h

  have hD :
      HasDerivAt
        (fun t : ℝ =>
          f t * deriv (deriv (deriv g)) t)
        0 0 := by
    convert df0.hasDerivAt.mul dg3.hasDerivAt
      using 1 <;> simp [f0, f1]

  let E : ℝ → ℂ := fun t =>
    deriv (deriv (deriv f)) t * g t +
    (3 : ℂ) *
      (deriv (deriv f) t * deriv g t) +
    (3 : ℂ) *
      (deriv f t * deriv (deriv g) t) +
    f t * deriv (deriv (deriv g)) t

  have hE : HasDerivAt E 0 0 := by
    have hsum := ((hA.add hB).add hC).add hD
    convert hsum using 1 <;>
      simp only [E, Pi.add_apply, add_zero]

  have hfnear :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        ContDiffAt ℝ 4 f t :=
    hf.eventually (by simp)

  have hgnear :
      ∀ᶠ t in 𝓝 (0 : ℝ),
        ContDiffAt ℝ 4 g t :=
    hg.eventually (by simp)

  have hthird :
      deriv (deriv (deriv
        (fun t : ℝ => f t * g t))) =ᶠ[𝓝 0]
      E := by
    filter_upwards [hfnear, hgnear]
      with t hft hgt
    dsimp only [E]
    convert p83_local_leibniz_third
      f g t hft hgt using 1 <;>
      simp only [mul_assoc]

  have hfourth :
      deriv (deriv (deriv (deriv
        (fun t : ℝ => f t * g t)))) 0 = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hthird]
    exact hE.deriv

  simpa only
    [iteratedDeriv_succ, iteratedDeriv_zero]
    using hfourth

#print axioms p83_local_fourth_product_zero

end Lanzarini
