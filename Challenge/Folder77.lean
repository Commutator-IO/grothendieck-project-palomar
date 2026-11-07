module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder77

open MvPolynomial Matrix

/-- The polar matrix of the quadratic form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` over a
commutative ring `R`. -/
def polarOf {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then 2 * y s(i, i) else y s(i, j)

section

open Finset

/-- The fixed-point-free involutions of `Fin m`, that is, the perfect matchings. -/
def fpfInv (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i

end

/-- The hafnian of the off-diagonal variables: the sum over the perfect matchings of
`Fin m` (the fixed-point-free involutions) of the products of the `Yᵢⱼ`. -/
noncomputable def hafnian (m : ℕ) : MvPolynomial (Sym2 (Fin m)) ℤ :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ Finset.univ.filter (fun i => i < σ i), X s(i, σ i)

/-- **Pages 68–71, every even rank, over any base.** There is `C ∈ ℤ[Y]` such that for every
commutative ring `R` and every form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` of rank `2n` over `R`,
`(-1)ⁿ det P(y) = B(y)² - 4 C(y)`. -/
theorem disc_even_rank (n : ℕ) :
    ∃ C : MvPolynomial (Sym2 (Fin (2 * n))) ℤ, ∀ {R : Type*} [CommRing R]
      (y : Sym2 (Fin (2 * n)) → R),
        (-1) ^ n * (polarOf y).det = aeval y (hafnian (2 * n)) ^ 2 - 4 * aeval y C := by
  sorry

end Grothendieck.Folder77
