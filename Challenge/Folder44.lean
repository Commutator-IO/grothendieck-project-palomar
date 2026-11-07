module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder44

/-- `Δ = {±3e₁, ±3e₂, ±(e₁ + e₂), ±(e₁ - e₂)}`. -/
def roots : Finset (ℤ × ℤ) :=
  {(3, 0), (-3, 0), (0, 3), (0, -3), (1, 1), (-1, -1), (1, -1), (-1, 1)}

/-- **The three axioms do not give integrality.** There is a finite reduced `Δ`
generating `ℤ²`, with a symmetry for each root, whose (unique) symmetry of the form
`x ↦ x - f(x) a` has a non-integral Cartan number. -/
theorem axioms_not_integral :
    AddSubgroup.closure (roots : Set (ℤ × ℤ)) = ⊤ ∧
    (∀ a ∈ roots, -a ∈ roots) ∧
    (∀ a ∈ roots, ∀ b ∈ roots, ∀ q : ℚ,
      (b.1 : ℚ) = q * a.1 ∧ (b.2 : ℚ) = q * a.2 → q = 1 ∨ q = -1) ∧
    (∀ a ∈ roots, ∃ S : (ℤ × ℤ) ≃+ (ℤ × ℤ), S a = -a ∧ ∀ x ∈ roots, S x ∈ roots) ∧
    ∀ f : ℤ × ℤ →+ ℚ, f (3, 0) = 2 →
      (∀ x ∈ roots, ∃ y ∈ roots, (x.1 : ℚ) - f x * 3 = y.1 ∧ (x.2 : ℚ) = y.2) →
      ¬ ∃ n : ℤ, f (1, 1) = n := by
  sorry

end Grothendieck.Folder44
