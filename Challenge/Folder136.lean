module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder136

/-- **Théorème 1 (p. 22).** If `binom(j, i)(x_j − x_i) = 0` for all `j > i ≥ N` in an
abelian group, then `x_j = x_N` for every `j ≥ N`. -/
theorem binomial_constant {A : Type*} [AddCommGroup A] (x : ℕ → A) (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (x j - x i) = 0) :
    ∀ j, N ≤ j → x j = x N := by
  sorry

end Grothendieck.Folder136

open TensorProduct Coalgebra WithConv Polynomial Finset
