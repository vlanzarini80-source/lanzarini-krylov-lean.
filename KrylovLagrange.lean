
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

Uses mathlib v4.24.0's Complex.star_def
for conjugation.
No artificial axioms or additional hypotheses.
Verified by GitHub Actions #78.
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
  simp only [
    Complex.star_def,
    Complex.normSq_apply,
    Complex.mul_re,
    Complex.mul_im,
    Complex.sub_re,
    Complex.sub_im,
    Complex.add_re,
    Complex.add_im,
    Complex.conj_re,
    Complex.conj_im
  ]
  ring

/-!
P69: Finite-dimensional complex Lagrange identity.
Status: revised candidate.

The proof does not assume the Gram identity.
It expands each determinant, rearranges finite
sums and proves pair counting separately.
-/

/--
P69.1: Ordered-pair Lagrange identity
over the complex numbers.
-/
theorem krylovLagrange_ordered_complex
    {n : ℕ} (u v : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      star (krylovGramCoordinate u v i j) *
        krylovGramCoordinate u v i j) =
      2 * ((∑ i : Fin n, star (u i) * u i) *
             (∑ j : Fin n, star (v j) * v j) -
           (∑ i : Fin n, star (u i) * v i) *
             (∑ j : Fin n, star (v j) * u j)) := by
  let A : Fin n → ℂ :=
    fun i => star (u i) * u i
  let B : Fin n → ℂ :=
    fun i => star (v i) * v i
  let C : Fin n → ℂ :=
    fun i => star (u i) * v i
  let D : Fin n → ℂ :=
    fun i => star (v i) * u i

  have hpoint (i j : Fin n) :
      star (krylovGramCoordinate u v i j) *
          krylovGramCoordinate u v i j =
        A i * B j + A j * B i -
          C i * D j - C j * D i := by
    simp only [
      krylovGramCoordinate,
      star_sub,
      star_mul
    ]
    dsimp [A, B, C, D]
    ring

  have hprod (p q : Fin n → ℂ) :
      (∑ i : Fin n, ∑ j : Fin n,
        p i * q j) =
        (∑ i : Fin n, p i) *
          (∑ j : Fin n, q j) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]

  have hprod_swap (p q : Fin n → ℂ) :
      (∑ i : Fin n, ∑ j : Fin n,
        p j * q i) =
        (∑ i : Fin n, p i) *
          (∑ j : Fin n, q j) := by
    calc
      _ = ∑ j : Fin n, ∑ i : Fin n,
          p j * q i := Finset.sum_comm
      _ = _ := hprod p q

  change
    (∑ i : Fin n, ∑ j : Fin n,
      star (krylovGramCoordinate u v i j) *
        krylovGramCoordinate u v i j) =
      2 * ((∑ i : Fin n, A i) *
             (∑ j : Fin n, B j) -
           (∑ i : Fin n, C i) *
             (∑ j : Fin n, D j))

  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (A i * B j + A j * B i -
            C i * D j - C j * D i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint i j
    _ = 2 * ((∑ i : Fin n, A i) *
               (∑ j : Fin n, B j) -
             (∑ i : Fin n, C i) *
               (∑ j : Fin n, D j)) := by
        simp only [
          Finset.sum_add_distrib,
          Finset.sum_sub_distrib
        ]
        rw [
          hprod A B,
          hprod_swap A B,
          hprod C D,
          hprod_swap C D
        ]
        ring

/--
P69.2: Real ordered-pair identity
derived from P69.1.
-/
theorem krylovLagrange_ordered_normSq
    {n : ℕ} (u v : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
       Complex.normSq
         (krylovGramCoordinate u v i j)) =
      2 * ((∑ i : Fin n,
              Complex.normSq (u i)) *
             (∑ j : Fin n,
              Complex.normSq (v j)) -
           Complex.normSq
             (∑ i : Fin n,
               star (u i) * v i)) := by
  apply Complex.ofReal_inj.mp
  simp only [
    Complex.ofReal_sum,
    Complex.ofReal_mul,
    Complex.ofReal_sub,
    Complex.ofReal_ofNat,
    Complex.normSq_eq_conj_mul_self,
    ← Complex.star_def,
    star_sum,
    star_mul,
    star_star
  ]
  convert krylovLagrange_ordered_complex u v
    using 1 <;> ring

/--
P69.3: A symmetric finite double sum
with zero diagonal counts each upper
triangular entry exactly twice.
-/
private theorem krylov_symmetric_double_sum
    {n : ℕ}
    (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    (∑ i : Fin n, ∑ j : Fin n, f i j) =
      2 * (∑ i : Fin n,
        ∑ j ∈ Finset.univ.filter
          (fun j : Fin n => i < j),
          f i j) := by
  classical

  let g : Fin n → Fin n → ℝ :=
    fun i j => if i < j then f i j else 0

  let h : Fin n → Fin n → ℝ :=
    fun i j => if j < i then f i j else 0

  have hpoint (i j : Fin n) :
      f i j = g i j + h i j := by
    rcases lt_trichotomy i j with
      hij | heq | hji
    · simp [g, h, hij, not_lt_of_ge hij.le]
    · subst j
      simp [g, h, hdiag]
    · simp [g, h, hji, not_lt_of_ge hji.le]

  have hrev :
      (∑ i : Fin n, ∑ j : Fin n,
        h i j) =
      (∑ i : Fin n, ∑ j : Fin n,
        g i j) := by
    calc
      _ = ∑ j : Fin n, ∑ i : Fin n,
          h i j := Finset.sum_comm
      _ = ∑ j : Fin n, ∑ i : Fin n,
          g j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        simp only [h, g, hsym i j]
      _ = _ := rfl

  calc
    (∑ i : Fin n, ∑ j : Fin n,
      f i j) =
        (∑ i : Fin n, ∑ j : Fin n,
          (g i j + h i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint i j
    _ = (∑ i : Fin n, ∑ j : Fin n,
          g i j) +
        (∑ i : Fin n, ∑ j : Fin n,
          h i j) := by
      simp_rw [Finset.sum_add_distrib]
    _ = 2 * (∑ i : Fin n, ∑ j : Fin n,
          g i j) := by
      rw [hrev]
      ring
    _ = _ := by
      simp only [g, Finset.sum_filter]

/--
P69.4: Finite-dimensional complex
Lagrange identity.

No normalization or Jacobi-dynamics
assumption is needed.
-/
theorem krylovLagrange_finite
    {n : ℕ} (u v : Fin n → ℂ) :
    krylovGramSum u v =
      (∑ i : Fin n,
        Complex.normSq (u i)) *
        (∑ j : Fin n,
          Complex.normSq (v j)) -
      Complex.normSq
        (∑ i : Fin n,
          star (u i) * v i) := by

  have hsym (i j : Fin n) :
      Complex.normSq
        (krylovGramCoordinate u v i j) =
      Complex.normSq
        (krylovGramCoordinate u v j i) := by
    rw [krylovGramCoordinate_swap]
    simp

  have hdiag (i : Fin n) :
      Complex.normSq
        (krylovGramCoordinate u v i i) =
          0 := by
    rw [krylovGramCoordinate_self]
    simp

  have htriangle :
      (∑ i : Fin n, ∑ j : Fin n,
        Complex.normSq
          (krylovGramCoordinate u v i j)) =
          2 * krylovGramSum u v := by
    simpa only [krylovGramSum] using
      (krylov_symmetric_double_sum
        (fun i j =>
          Complex.normSq
            (krylovGramCoordinate u v i j))
        hsym hdiag)

  have hordered :=
    krylovLagrange_ordered_normSq u v
  rw [htriangle] at hordered
  nlinarith

end Lanzarini
