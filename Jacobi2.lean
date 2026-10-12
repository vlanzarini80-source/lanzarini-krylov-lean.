import Lean

-- Two-site Jacobi matrix with arbitrary integer coefficients.
def jacobi2 (a0 a1 b : Int) (i j : Bool) : Int :=
  match i, j with
  | false, false => a0
  | false, true  => b
  | true, false  => b
  | true, true   => a1

-- Symmetry must be derived from the definition.
theorem jacobi2_symmetric (a0 a1 b : Int) (i j : Bool) :
    jacobi2 a0 a1 b i j = jacobi2 a0 a1 b j i := by
  cases i <;> cases j <;> rfl
