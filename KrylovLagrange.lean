
import Mathlib
import KrylovGram

namespace Lanzarini

/--
P66.1: Two-coordinate complex Lagrange identity,
expanded into real and imaginary components.

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
P67.2: Product of Hermitian inner-product
sums equals the corresponding double sum.
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

/--
P68.1: Complex two-coordinate Lagrange identity.

This is an identity over arbitrary complex
numbers a, b, c and d.

The proof reduces it to the real polynomial
identity already established in P66.1.
-/
theorem krylovLagrange_two_coordinates_complex
    (a b c d : ℂ) :
    Complex.normSq (a * d - b * c)
    =
    (Complex.normSq a + Complex.normSq b) *
      (Complex.normSq c + Complex.normSq d)
      -
    Complex.normSq
      (star a * c + star b * d) := by
  rw [show star a = conj a from rfl]
  rw [show star b = conj b from rfl]
  change
    (a.re * d.re - a.im * d.im -
      b.re * c.re + b.im * c.im) ^ 2 +
    (a.re * d.im + a.im * d.re -
      b.re * c.im - b.im * c.re) ^ 2
    =
    ((a.re ^ 2 + a.im ^ 2) +
      (b.re ^ 2 + b.im ^ 2)) *
    ((c.re ^ 2 + c.im ^ 2) +
      (d.re ^ 2 + d.im ^ 2)) -
    ((a.re * c.re + a.im * c.im) +
      (b.re * d.re + b.im * d.im)) ^ 2 -
    ((a.re * c.im - a.im * c.re) +
      (b.re * d.im - b.im * d.re)) ^ 2
  exact krylovLagrange_two_coordinates_real
    a.re a.im b.re b.im c.re c.im d.re d.im

end Lanzarini
