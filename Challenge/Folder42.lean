module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder42.Reseau

open AlgebraicGeometry CategoryTheory Limits Topology

universe u

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- **A homomorphism of réseaux of local rings `p(X) → p(Y)` over `p(S)` (page 1).** An
application of the specialisation orders, increasing (`x ⤳ x'`, « `x'` specialises `x` »,
gives `φ x ⤳ φ x'`), lying over `S`, with a local homomorphism `𝒪_{Y,φ(x)} → 𝒪_{X,x}` at each
point, compatible with the generisation maps, and compatible with the structure maps to the
local rings of `S`. The localisation axiom of a réseau is a property of `p(X)` and `p(Y)`, which
come from schemes, so it is not a field here. -/
structure ReseauHom where
  toFun : X → Y
  mono : ∀ {x x' : X}, x ⤳ x' → toFun x ⤳ toFun x'
  liesOver : ∀ x, sX x = sY (toFun x)
  stalk : ∀ x, Y.presheaf.stalk (toFun x) ⟶ X.presheaf.stalk x
  isLocalHom : ∀ x, IsLocalHom (stalk x).hom
  compat : ∀ {x x' : X} (h : x ⤳ x'),
    stalk x' ≫ X.presheaf.stalkSpecializes h = Y.presheaf.stalkSpecializes (mono h) ≫ stalk x
  overStalk : ∀ x, sY.stalkMap (toFun x) ≫ stalk x =
    S.presheaf.stalkSpecializes (Inseparable.of_eq (liesOver x)).specializes ≫ sX.stalkMap x

attribute [instance] ReseauHom.isLocalHom

variable {sX sY}

/-- The réseau homomorphism of an `S`-morphism. -/
noncomputable def toReseau (f : X ⟶ Y) (hf : f ≫ sY = sX) : ReseauHom sX sY where
  toFun := f
  mono h := f.base.hom.map_specializes h
  liesOver x := by rw [← hf]; rfl
  stalk x := f.stalkMap x
  isLocalHom x := inferInstance
  compat h := (f.stalkSpecializes_stalkMap _ _ h).symm
  overStalk x := by
    subst hf
    rw [Scheme.Hom.stalkMap_comp]
    simp

/-- **Corollaire 3, the theorem of page 2 in the edition's form.** For `X` locally Noetherian and
`Y` locally of finite type and separated over `S`, `f ↦ p(f)` is a bijection from the
`S`-morphisms `X → Y` onto the homomorphisms of réseaux of local rings `p(X) → p(Y)` over
`p(S)`. -/
theorem toReseau_bijective [IsLocallyNoetherian X] [LocallyOfFiniteType sY] [IsSeparated sY] :
    Function.Bijective (fun f : {f : X ⟶ Y // f ≫ sY = sX} => toReseau f.1 f.2) := by
  sorry

end Grothendieck.Folder42.Reseau
