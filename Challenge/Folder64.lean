module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder64

open Finset

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- The four vertices other than `∞` and `−1`. -/
def quad (i : K) : Finset K := {0, 1, i, -i}

variable {i : K}

/-- Page 48: an automorphism fixing `∞` and `−1` is `z ↦ a z + (a − 1)`; if it maps
`{0, 1, i, −i}` into itself, then `5 (a − 1) = 0`. -/
theorem fixer_five (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (a : K)
    (h : ∀ z ∈ quad i, a * z + (a - 1) ∈ quad i) : (5 : K) * (a - 1) = 0 := by
  sorry

end Field

end Grothendieck.Folder64
