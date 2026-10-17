
import Mathlib
import KrylovGram

namespace Lanzarini

/--
P66.1: Two-coordinate complex Lagrange identity,
expanded into real and imaginary components.

a = ar + i * ai
b = br + i * bi
c = cr + i * ci
d = dr + i * di

Left side: squared modulus of a*d - b*c.

Right side: product of squared vector norms
minus squared modulus of the Hermitian
inner product conj(a)*c + conj(b)*d.

No additional hypotheses are required.
-/
theorem krylovLagrange_two_coordinates_real
    (ar ai br bi cr ci dr di : ℝ) :
    (ar * dr - ai * di - br * cr + bi * ci) ^ 2
      +
    (ar * di + ai * dr - br * ci - bi * cr) ^ 2
    =
    ((ar ^ 2 + ai ^ 2) + (br ^ 2 + bi ^ 2))
      *
    ((cr ^ 2 + ci ^ 2) + (dr ^ 2 + di ^ 2))
      -
    ((ar * cr + ai * ci) +
      (br * dr + bi * di)) ^ 2
      -
    ((ar * ci - ai * cr) +
      (br * di - bi * dr)) ^ 2 := by
  ring

/--
P67.1: Product of finite squared-norm sums
equals the corresponding double sum.

Valid for arbitrary finite dimensions.
-/
theorem krylovLagrange_norm_product_expansion
    {n : ℕ}
    (u v : Fin n → ℂ) :
    (∑ i : Fin n, Complex.normSq (u i)) *
      (∑ j : Fin n, Complex.normSq (v j))
    =
    ∑ i : Fin n,
      ∑ j : Fin n,
        Complex.normSq (u i) *
          Complex.normSq (v j) := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

/--
P67.2: Product of the two Hermitian
inner-product sums equals a double sum.

No normalization or dynamical hypotheses.
-/
theorem krylovLagrange_inner_product_expansion
    {n : ℕ}
    (u v : Fin n → ℂ) :
    (∑ i : Fin n, star (u i) * v i) *
      (∑ j : Fin n, star (v j) * u j)
    =
    ∑ i : Fin n,
      ∑ j : Fin n,
        (star (u i) * v i) *
          (star (v j) * u j) := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

end Lanzarini
