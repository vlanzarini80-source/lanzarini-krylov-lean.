
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Lanzarini

/-!
P83 local fourth-order bridge.
Preliminary regularity verification only.
-/

#check iteratedDeriv_succ
#check iteratedDeriv_succ'
#check iteratedDeriv_zero
#check iteratedDeriv_one

#check iteratedDeriv_vcomp_eq_sum_orderedFinpartition
#check iteratedDeriv_comp_eq_sum_orderedFinpartition

theorem p83_local_product_smoothness
    (f g : ℝ → ℂ)
    (hf : ContDiffAt ℝ 4 f 0)
    (hg : ContDiffAt ℝ 4 g 0) :
    ContDiffAt ℝ 4
      (fun t : ℝ => f t * g t) 0 := by
  exact hf.mul hg

#print axioms p83_local_product_smoothness

end Lanzarini
