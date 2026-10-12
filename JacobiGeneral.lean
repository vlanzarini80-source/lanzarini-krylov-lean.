import Lean

-- Jacobi matrix entries for indices in Fin n.
-- The off-diagonal coefficient is indexed by the smaller site.
def jacobiEntry {n : Nat}
    (a b : Fin n → Int) (i j : Fin n) : Int :=
  if i = j then a i
  else if i.val + 1 = j.val then b i
  else if j.val + 1 = i.val then b j
  else 0

-- Symmetry is proved from the definition, not assumed.
theorem jacobiEntry_symmetric {n : Nat}
    (a b : Fin n → Int) (i j : Fin n) :
    jacobiEntry a b i j = jacobiEntry a b j i := by
  unfold jacobiEntry
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
