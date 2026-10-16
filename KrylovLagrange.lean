
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

end Lanzarini
