
import P75_1_Orthogonality

namespace Lanzarini

/-!
P75.2a: Verification of dependencies for
real orthogonality of the physical velocity.

Target:
Re ⟪psi(t), (-iH) psi(t)⟫ = 0.

This file is a dependency probe.
It does not yet establish the target theorem.
-/

-- Hermiticity of the Jacobi Hamiltonian.
#check jacobiComplex_conjTranspose

-- Anti-Hermiticity of the evolution generator.
#check jacobiEvolutionGenerator_conjTranspose

-- Conservation of the Jacobi inner product.
#check jacobiInner_state_self

-- Conservation of squared norm.
#check jacobiNormSq_state

-- Physical state derivative.
#check p73_jacobiState_hasDerivAt

-- Previously verified centered-state orthogonality.
#check p75_centeredState_orthogonal

-- Matrix/vector identities needed for the proof.
#check Matrix.star_mulVec
#check Matrix.dotProduct_mulVec
#check Matrix.vecMul_vecMul

end Lanzarini
