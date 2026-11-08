
import P81_2b3_PhysicalKrylovDerivative
import Mathlib

namespace Lanzarini

/-!
P83.5b: API inspection for physical regularity.

No assumed physical coefficients.
No sorry, admit, or new axioms.
No theorem claimed.
-/

#check NormedSpace.exp
#check contDiff_exp
#check ContDiff.comp
#check ContDiffAt.comp
#check ContinuousLinearMap.contDiff
#check contDiff_const
#check contDiff_id
#check ContDiff.mul
#check ContDiff.sum
#check Complex.normSq

end Lanzarini
