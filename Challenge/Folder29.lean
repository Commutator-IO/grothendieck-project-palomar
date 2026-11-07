module

public import Mathlib

@[expose] public section

open Matrix

namespace Folder29

variable {C C' : Type*} [Fintype C] [Fintype C']

/-- The map `ℤ_ℓ^C → ℤ_ℓ^{C'}` of an integer matrix with rows indexed by `C'` and columns
by `C`. -/
noncomputable def inertiaMap (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (C → ℤ_[ℓ]) → (C' → ℤ_[ℓ]) :=
  (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVec

/-- **The criterion of page 120.** The integer matrix `N` is bijective over `ℤ_ℓ` for every
prime `ℓ ≠ p` iff `card C = card C'` and, the columns being matched with the rows by some
bijection, `det N = ± p^k`. -/
theorem criterion [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      Fintype.card C = Fintype.card C' ∧ ∃ e : C' ≃ C, ∃ k : ℕ,
        (N.submatrix id e).det = p ^ k ∨ (N.submatrix id e).det = -(p ^ k : ℤ) := by
  sorry

end Folder29
