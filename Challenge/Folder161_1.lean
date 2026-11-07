module

public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Tactic.TFAE
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

@[expose] public section

namespace Grothendieck.Folder161_1

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {u : E ⥤ F} {v : F ⥤ E} (adj : u ⊣ v)

section Contractions

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- The action of a scalar `e ∈ End(𝟙)` on an object `X`. -/
def scalar (e : 𝟙_ C ⟶ 𝟙_ C) (X : C) : X ⟶ X :=
  (λ_ X).inv ≫ e ▷ X ≫ (λ_ X).hom

/-- If `Y ⊗ X ≅ 𝟙` and `X ⊗ Y ≅ 𝟙`, tensoring on the left with `X` is an
equivalence, with quasi-inverse tensoring with `Y`. -/
def tensorLeftEquivOfInverse {X Y : C} (i : Y ⊗ X ≅ 𝟙_ C) (j : X ⊗ Y ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft X) (tensorLeft Y)
    (NatIso.ofComponents (fun Z => (λ_ Z).symm ≪≫ whiskerRightIso i.symm Z ≪≫ α_ Y X Z)
      (by
        intro _ _ f
        dsimp
        simp only [whiskerRightIso_hom, Iso.symm_hom, Category.assoc]
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
        simp))
    (NatIso.ofComponents (fun Z => (α_ X Y Z).symm ≪≫ whiskerRightIso j Z ≪≫ λ_ Z)
      (by
        intro _ _ f
        dsimp
        simp only [whiskerRightIso_hom, Category.assoc]
        rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
        simp))

variable [SymmetricCategory C] {L L' : C}

open BraidedCategory

/-- `φ_{L',L} = φ_{L,L'} ∘ s_{L',L}`, the trivialisation of `L' ⊗ L` through the
symmetry (page 12). -/
def phiSwap (φ : L ⊗ L' ≅ 𝟙_ C) : L' ⊗ L ≅ 𝟙_ C := β_ L' L ≪≫ φ

/-- Tensoring with an invertible `L` is fully faithful. -/
def fullyFaithfulL (φ : L ⊗ L' ≅ 𝟙_ C) : (tensorLeft L).FullyFaithful :=
  (tensorLeftEquivOfInverse (phiSwap φ) φ).fullyFaithfulFunctor

/-- `ψ_{L',L} : L' ⊗ L ≅ 𝟙`, defined by the triangle identity
`φ_{L,L'} ⊗ id_L = id_L ⊗ ψ_{L',L}` (page 12). -/
def psi (φ : L ⊗ L' ≅ 𝟙_ C) : L' ⊗ L ≅ 𝟙_ C :=
  (fullyFaithfulL φ).preimageIso
    ((α_ L L' L).symm ≪≫ whiskerRightIso φ L ≪≫ λ_ L ≪≫ (ρ_ L).symm)

/-- **Page 12, « Relations entre `φ_{L',L}` et `ψ_{L',L}` ? »** For a scalar `e`,
`φ_{L',L} = e · ψ_{L',L}` if and only if the symmetry acts on `L ⊗ L` by `e`. -/
theorem phiSwap_eq_iff (φ : L ⊗ L' ≅ 𝟙_ C) (e : 𝟙_ C ⟶ 𝟙_ C) :
    (phiSwap φ).hom = (psi φ).hom ≫ e ↔ (β_ L L).hom = scalar e (L ⊗ L) := by
  sorry

end Contractions

end Grothendieck.Folder161_1
