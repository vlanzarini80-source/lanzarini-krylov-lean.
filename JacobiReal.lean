import Mathlib

namespace Lanzarini

def jacobiRealEntry {n : ℕ}
    (a b : Fin n → ℝ) (i j : Fin n) : ℝ :=
  if i = j then a i
  else if i.val + 1 = j.val then b i
  else if j.val + 1 = i.val then b j
  else 0

def jacobiReal (n : ℕ)
    (a b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => jacobiRealEntry a b i j

theorem jacobiRealEntry_symmetric {n : ℕ}
    (a b : Fin n → ℝ) (i j : Fin n) :
    jacobiRealEntry a b i j =
      jacobiRealEntry a b j i := by
  unfold jacobiRealEntry
  by_cases h : i = j
  · subst j
    simp
  · have h' : j ≠ i := Ne.symm h
    simp only [if_neg h, if_neg h']
    by_cases h₁ : i.val + 1 = j.val
    · have h₂ : j.val + 1 ≠ i.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val + 1 = i.val
      · simp [h₁, h₂]
      · simp [h₁, h₂]

theorem jacobiReal_transpose {n : ℕ}
    (a b : Fin n → ℝ) :
    (jacobiReal n a b).transpose = jacobiReal n a b := by
  ext i j
  exact (jacobiRealEntry_symmetric a b j i)

end Lanzarini
