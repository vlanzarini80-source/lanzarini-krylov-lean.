
import Mathlib
import P81_2b3_CenteredMinorDerivative

namespace Lanzarini

/-!
P83.5c: regularity API diagnostic.

No P79.
No assumed Taylor coefficients.
No sorry, admit, or new axioms.

This file does not prove C^4 regularity.
-/

#check NormedSpace.exp
#check ContDiff
#check ContDiffAt
#check ContDiff.comp
#check ContDiffAt.comp
#check ContDiff.add
#check ContDiff.mul

#check p81_2_state
#check p81_2b3_K
#check p81_2_state_hasDerivAt

end Lanzarini
