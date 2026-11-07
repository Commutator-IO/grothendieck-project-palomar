module

public import Mathlib

@[expose] public section

open Finset IsLocalRing

namespace Grothendieck.Folder46

section Cocycles

variable {Γ A : Type*} [Group Γ] [Ring A] [MulSemiringAction Γ A]

/-- A (nonabelian) 1-cocycle of `Γ` with values in `Aˣ`: `c(gh) = c(g) · g(c(h))`. -/
def IsCocycle (c : Γ → Aˣ) : Prop :=
  ∀ g h, (c (g * h) : A) = c g * g • (c h : A)

variable [Fintype Γ]

variable {B : Type*} [Ring B] [MulSemiringAction Γ B]

end Cocycles

section LocalRing

variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]

variable [IsLocalRing O]

variable {Γ B : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ A] [Ring B]
  [MulSemiringAction Γ B]

/-- **Page 90, injectivity**, `A` finite over `𝒪` and `p ∤ |Γ|`: two cocycles `Γ → A*` whose
images in `B = A/𝔪A` (or any surjective equivariant image with kernel in `𝔪A`) are cohomologous
are cohomologous. -/
theorem injective [Module.Finite O A] (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ)
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A)) {c c' : Γ → Aˣ}
    (hc : IsCocycle c) (hc' : IsCocycle c')
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * π (c' g) * g • (v : B)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  sorry

end LocalRing

end Grothendieck.Folder46
