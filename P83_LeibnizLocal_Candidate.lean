
import P83_LeibnizSecond_Candidate
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

namespace Lanzarini

/-!
P83 local Leibniz bridge.

Stage 1:
Local differentiability of iterated derivatives.

Stage 2:
Local third-order Leibniz identity.

No P79.
No physical coefficients.
No sorry or admit.
No additional axioms.

Candidate requiring Lean CI verification.
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

/--
Local third-order Leibniz formula.

The hypotheses are local ContDiffAt conditions.

The second-order identity is obtained
from the previously verified Leibniz theorem
at points in a neighborhood of x.

No global differentiability is assumed.
-/
theorem p83_local_leibniz_third
    (f g : ℝ → ℂ) (x : ℝ)
    (hf : ContDiffAt ℝ 4 f x)
    (hg : ContDiffAt ℝ 4 g x) :
    deriv (deriv (deriv
      (fun t : ℝ => f t * g t))) x =
      deriv (deriv (deriv f)) x * g x +
      (3 : ℂ) * deriv (deriv f) x * deriv g x +
      (3 : ℂ) * deriv f x * deriv (deriv g) x +
      f x * deriv (deriv (deriv g)) x := by

  have hfnear :
      ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 4 f y :=
    hf.eventually (by simp)

  have hgnear :
      ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 4 g y :=
    hg.eventually (by simp)

  have hsecond :
      deriv (deriv
        (fun t : ℝ => f t * g t)) =ᶠ[𝓝 x]
        (fun t : ℝ =>
          deriv (deriv f) t * g t +
          (2 : ℂ) * deriv f t * deriv g t +
          f t * deriv (deriv g) t) := by

    filter_upwards [hfnear, hgnear]
      with y hfy hgy

    have hfy0 :=
      p83_local_diff_iterated
        f y 0 hfy (by omega)

    have hgy0 :=
      p83_local_diff_iterated
        g y 0 hgy (by omega)

    have hfy1 :=
      p83_local_diff_iterated
        f y 1 hfy (by omega)

    have hgy1 :=
      p83_local_diff_iterated
        g y 1 hgy (by omega)

    have hf_eventually :
        ∀ᶠ z in 𝓝 y,
          DifferentiableAt ℝ f z := by
      filter_upwards
        [p83_local_eventually_diff
          f y 0 hfy (by omega)]
        with z hz
      simpa only [iteratedDeriv_zero] using hz

    have hg_eventually :
        ∀ᶠ z in 𝓝 y,
          DifferentiableAt ℝ g z := by
      filter_upwards
        [p83_local_eventually_diff
          g y 0 hgy (by omega)]
        with z hz
      simpa only [iteratedDeriv_zero] using hz

    have hfy_diff :
        DifferentiableAt ℝ f y := by
      simpa only [iteratedDeriv_zero] using hfy0

    have hgy_diff :
        DifferentiableAt ℝ g y := by
      simpa only [iteratedDeriv_zero] using hgy0

    have hdfy_diff :
        DifferentiableAt ℝ (deriv f) y := by
      simpa only [
        iteratedDeriv_succ,
        iteratedDeriv_zero
      ] using hfy1

    have hdgy_diff :
        DifferentiableAt ℝ (deriv g) y := by
      simpa only [
        iteratedDeriv_succ,
        iteratedDeriv_zero
      ] using hgy1

    exact p83_leibniz_second
      f g y
      hf_eventually
      hg_eventually
      hfy_diff
      hgy_diff
      hdfy_diff
      hdgy_diff

  rw [Filter.EventuallyEq.deriv_eq hsecond]

  have df0 :
      DifferentiableAt ℝ f x := by
    simpa only [iteratedDeriv_zero] using
      p83_local_diff_iterated
        f x 0 hf (by omega)

  have dg0 :
      DifferentiableAt ℝ g x := by
    simpa only [iteratedDeriv_zero] using
      p83_local_diff_iterated
        g x 0 hg (by omega)

  have df1 :
      DifferentiableAt ℝ (deriv f) x := by
    simpa only [
      iteratedDeriv_succ,
      iteratedDeriv_zero
    ] using
      p83_local_diff_iterated
        f x 1 hf (by omega)

  have dg1 :
      DifferentiableAt ℝ (deriv g) x := by
    simpa only [
      iteratedDeriv_succ,
      iteratedDeriv_zero
    ] using
      p83_local_diff_iterated
        g x 1 hg (by omega)

  have df2 :
      DifferentiableAt ℝ
        (deriv (deriv f)) x := by
    simpa only [
      iteratedDeriv_succ,
      iteratedDeriv_zero
    ] using
      p83_local_diff_iterated
        f x 2 hf (by omega)

  have dg2 :
      DifferentiableAt ℝ
        (deriv (deriv g)) x := by
    simpa only [
      iteratedDeriv_succ,
      iteratedDeriv_zero
    ] using
      p83_local_diff_iterated
        g x 2 hg (by omega)

  have hA :
      DifferentiableAt ℝ
        (deriv (deriv f) * g) x :=
    df2.mul dg0

  have hB :
      DifferentiableAt ℝ
        (deriv f * deriv g) x :=
    df1.mul dg1

  have hC :
      DifferentiableAt ℝ
        (f * deriv (deriv g)) x :=
    df0.mul dg2

  have hB2 :
      DifferentiableAt ℝ
        (fun t : ℝ =>
          (2 : ℂ) *
            (deriv f t * deriv g t)) x :=
    hB.const_mul 2

  have hsum :
      DifferentiableAt ℝ
        ((deriv (deriv f) * g) +
          (fun t : ℝ =>
            (2 : ℂ) *
              (deriv f t * deriv g t))) x :=
    hA.add hB2

  have hfun :
      (fun t : ℝ =>
        deriv (deriv f) t * g t +
          (2 : ℂ) * deriv f t * deriv g t +
          f t * deriv (deriv g) t) =
        ((deriv (deriv f) * g) +
          (fun t : ℝ =>
            (2 : ℂ) *
              (deriv f t * deriv g t)) +
          (f * deriv (deriv g))) := by
    funext t
    simp only [Pi.add_apply, Pi.mul_apply]
    ring

  rw [hfun]

  have hmiddle :
      deriv
        (fun t : ℝ =>
          (2 : ℂ) *
            (deriv f t * deriv g t)) x =
        (2 : ℂ) *
          (deriv (deriv f) x * deriv g x +
            deriv f x * deriv (deriv g) x) := by
    rw [deriv_const_mul]
    change
      (2 : ℂ) *
        deriv (deriv f * deriv g) x =
      (2 : ℂ) *
        (deriv (deriv f) x * deriv g x +
          deriv f x * deriv (deriv g) x)
    rw [deriv_mul df1 dg1]

  rw [deriv_add hsum hC]
  rw [deriv_add hA hB2]
  rw [deriv_mul df2 dg0]
  rw [hmiddle]
  rw [deriv_mul df0 dg2]
  ring

#print axioms p83_local_leibniz_third

end Lanzarini
