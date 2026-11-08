
import Mathlib
import P81_2b3_CenteredMinorDerivative

namespace Lanzarini

/-!
P83.5b - Physical regularity API probe.

Purpose:
Check the actual physical definitions
and basic differentiability interfaces.

No P79.
No expected Taylor coefficients.
No sorry, admit, or new axioms.

This file does not yet prove C^4 regularity.
-/

-- Matrix exponential used by Jacobi evolution.
#check NormedSpace.exp

-- Differentiability predicates.
#check ContDiff
#check ContDiffAt

-- Verified physical definitions.
#check p81_2_state
#check p81_2_velocity
#check p81_2b3_K
#check p81_2b2_rawMinor

-- Previously established physical derivatives.
#check p81_2_state_hasDerivAt
#check p81_2b1_velocity_hasDerivAt
#check p81_2b3_K_hasDerivAt
#check p81_2b2_rawMinor_hasDerivAt

end Lanzarini
