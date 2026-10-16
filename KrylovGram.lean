
import Mathlib
import KrylovNumber

namespace Lanzarini

/--
P65.1: Complex Gram coordinate.

The definition contains no complex conjugation.
-/
noncomputable def krylovGramCoordinate
    {n : ℕ}
    (u v : Fin n → ℂ)
    (i j : Fin n) : ℂ :=
  u i * v j - u j * v i

/--
P65.2: A Gram coordinate is antisymmetric.
-/
theorem krylovGramCoordinate_swap
    {n : ℕ}
    (u v : Fin n → ℂ)
    (i j : Fin n) :
    krylovGramCoordinate u v j i =
      -krylovGramCoordinate u v i j := by
  unfold krylovGramCoordinate
  ring

/--
P65.3: Diagonal Gram coordinates vanish.
-/
theorem krylovGramCoordinate_self
    {n : ℕ}
    (u v : Fin n → ℂ)
    (i : Fin n) :
    krylovGramCoordinate u v i i = 0 := by
  unfold krylovGramCoordinate
  ring

/--
P65.4: Every squared Gram coordinate
is nonnegative.
-/
theorem krylovGramCoordinate_normSq_nonneg
    {n : ℕ}
    (u v : Fin n → ℂ)
    (i j : Fin n) :
    0 ≤ Complex.normSq
      (krylovGramCoordinate u v i j) := by
  exact Complex.normSq_nonneg _

/--
P65.5: Finite sum of squared Gram coordinates.

Each unordered pair is counted once.
-/
noncomputable def krylovGramSum
    {n : ℕ}
    (u v : Fin n → ℂ) : ℝ :=
  ∑ i : Fin n,
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
      Complex.normSq (krylovGramCoordinate u v i j)

/--
P65.6: The Gram sum is nonnegative.

No dynamical assumption is used.
-/
theorem krylovGramSum_nonneg
    {n : ℕ}
    (u v : Fin n → ℂ) :
    0 ≤ krylovGramSum u v := by
  unfold krylovGramSum
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact Complex.normSq_nonneg _

end Lanzarini
