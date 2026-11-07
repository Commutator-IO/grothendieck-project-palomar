module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder78

open Polynomial Polynomial.Chebyshev

section Poly

variable (R : Type*) [CommRing R]

/-- The polynomial `F_n` of page 109: `F_{2m} = S_{m−1}`, `F_{2m+1} = S_m + S_{m−1}`, with
`S` the rescaled Chebyshev polynomials of the second kind. -/
noncomputable def F (n : ℤ) : R[X] :=
  if Even n then S R (n / 2 - 1) else S R (n / 2) + S R (n / 2 - 1)

end Poly

section Map

variable {k : Type*} [CommRing k]

/-- `u_α (x, y) = (1 − y + α x, x)`, as a permutation of `k²`. -/
def u (α : k) : Equiv.Perm (k × k) where
  toFun p := (1 - p.2 + α * p.1, p.1)
  invFun p := (p.2, 1 - p.1 + α * p.2)
  left_inv p := Prod.ext rfl (show 1 - (1 - p.2 + α * p.1) + α * p.1 = p.2 by ring)
  right_inv p := Prod.ext (show 1 - (1 - p.1 + α * p.2) + α * p.2 = p.1 by ring) rfl

/-- a) ⇔ d): **Théorème (p. 112)**, `u_α^n = id ⇔ F_n(α) = 0`, over any commutative ring. -/
theorem zpow_eq_one_iff (α : k) (n : ℤ) : u α ^ n = 1 ↔ (F k n).eval α = 0 := by
  sorry

end Map

end Grothendieck.Folder78
