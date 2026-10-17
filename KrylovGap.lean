
/-!
LANZARINI-KRYLOV-LEAN
P70: Exact Gram and scalar-channel decomposition.

This module extends the verified P69 Lagrange identity.
No theorem statements from P65-P69 are changed.

Status: candidate, pending Lean compilation.
-/

import KrylovLagrange

namespace Lanzarini

/--
P70.1: Exact real-part gap identity.

The real-projection gap is the sum of the
finite Gram contribution and the squared
imaginary part of the Hermitian pairing.

No normalization assumptions are required.
-/
theorem krylovGram_realPart_gap
    {n : ℕ} (u v : Fin n → ℂ) :
    (∑ i : Fin n, Complex.normSq (u i)) *
      (∑ i : Fin n, Complex.normSq (v i)) -
      ((∑ i : Fin n, star (u i) * v i).re) ^ 2 =
    krylovGramSum u v +
      ((∑ i : Fin n, star (u i) * v i).im) ^ 2 := by

  have h := krylovLagrange_finite u v

  rw [Complex.normSq_apply] at h

  nlinarith

/--
P70.2: Nonnegativity of the real-part gap.

This follows from P70.1 and the established
nonnegativity of the finite Gram sum.
-/
theorem krylovGram_realPart_gap_nonneg
    {n : ℕ} (u v : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, Complex.normSq (u i)) *
       (∑ i : Fin n, Complex.normSq (v i)) -
       ((∑ i : Fin n, star (u i) * v i).re) ^ 2 := by

  rw [krylovGram_realPart_gap]

  exact add_nonneg
    (krylovGramSum_nonneg u v)
    (sq_nonneg _)

end Lanzarini
