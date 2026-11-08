
import P83_5d_PhysicalRegularityStep1
import P83_5a_PhysicalCenteringBridge_Candidate
import Mathlib

namespace Lanzarini

/-!
P83.5e - Matrix exponential regularity probe.

Goal: identify the actual mathlib API
for deriving C^4 regularity from the
physical Jacobi evolution.

Diagnostic only.
No assumed physical coefficients.
No P79.
No sorry, admit, or new axioms.
-/

-- Existing physical evolution
#check jacobiPropagator
#check jacobiState
#check jacobiPropagator_complex_time_eq
#check p73_jacobiPropagator_hasDerivAt
#check p73_jacobiState_hasDerivAt

-- Existing physical state
#check p81_2_state
#check p81_2_velocity

-- Regularity interfaces
#check ContDiff
#check ContDiffAt
#check ContDiff.contDiffAt
#check ContDiff.comp
#check ContinuousLinearMap.contDiff

-- Exponential regularity candidates
#check NormedSpace.exp
#check contDiff_exp

-- Required final functions
#check p81_2b3_K
#check p81_2b2_rawMinor
#check p83_5a_physical_centering_fourth_zero

end Lanzarini
