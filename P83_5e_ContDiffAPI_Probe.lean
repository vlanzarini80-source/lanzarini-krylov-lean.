
import P83_5d_PhysicalRegularityStep1
import P83_5a_PhysicalCenteringBridge_Candidate
import Mathlib

namespace Lanzarini

/-!
P83.5e - Higher regularity API diagnostic.

Checks existing physical objects and
basic regularity interfaces.

No physical coefficient is assumed.
No sorry, admit, or new axioms.
-/

-- Verified source declarations to inspect
#check p81_2_state
#check p81_2_velocity
#check p81_2_state_hasDerivAt
#check p81_2b1_velocity_hasDerivAt

-- General regularity interfaces
#check ContDiff
#check ContDiffAt
#check ContDiff.contDiffAt

-- Elementary smooth functions
#check contDiff_const
#check contDiff_id

-- Physical functions requiring C^4
#check p81_2b3_K
#check p81_2b2_rawMinor

-- Existing conditional bridge
#check p83_5a_physical_centering_fourth_zero

end Lanzarini
