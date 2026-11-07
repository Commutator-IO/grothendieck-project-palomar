module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Defs

@[expose] public section

namespace Grothendieck.Folder114

open CategoryTheory Limits Function

universe u

/-- A class of functors between small categories (objects and arrows in
`Type u`). -/
abbrev ClasseDeFoncteurs : Type (u + 1) :=
  ∀ ⦃A B : Type u⦄ [Category.{u} A] [Category.{u} B], (A ⥤ B) → Prop

/-- `W₀`: the functors inducing a bijection on connected components. -/
def W₀ : ClasseDeFoncteurs.{u} := fun _ _ _ _ F => Bijective F.mapConnectedComponents

/-- A small category `A` is `W`-aspheric when `A → e` is in `W`. -/
def Aspherique (W : ClasseDeFoncteurs.{u}) (A : Type u) [Category.{u} A] : Prop :=
  W (Functor.star.{u} A)

/-- The product `a × b` of two representables in `Â`, computed objectwise:
`(a × b)(c) = Hom(c, a) × Hom(c, b)`. -/
@[simps obj]
def produitRep {A : Type u} [Category.{u} A] (a b : A) : Aᵒᵖ ⥤ Type u where
  obj c := (c.unop ⟶ a) × (c.unop ⟶ b)
  map f := TypeCat.ofHom fun x => (f.unop ≫ x.1, f.unop ≫ x.2)

/-- `A_{/X}` for a presheaf `X`: the category of pairs `(c, yoneda c → X)`. -/
abbrev Tranche {A : Type u} [Category.{u} A] (X : Aᵒᵖ ⥤ Type u) : Type u :=
  CostructuredArrow yoneda X

/-- `A` is *totally `W`-aspheric*: `W`-aspheric, and `a × b` is `W`-aspheric
in `Â` (i.e. `A_{/a×b}` is `W`-aspheric) for all `a, b`. -/
def TotalementAspherique (W : ClasseDeFoncteurs.{u}) (A : Type u) [Category.{u} A] : Prop :=
  Aspherique W A ∧ ∀ a b : A, Aspherique W (Tranche (produitRep a b))

/-- Condition (iii) of Proposition 4: `A` non-empty, and `a × b` `0`-connected
(`A_{/a×b}` non-empty and connected) for all `a, b`. -/
def ConditionIII (A : Type u) [Category.{u} A] : Prop :=
  Nonempty A ∧ ∀ a b : A, IsConnected (Tranche (produitRep a b))

/-- Inclusion of classes of functors. -/
def Inclus (W W' : ClasseDeFoncteurs.{u}) : Prop :=
  ∀ ⦃A B : Type u⦄ [Category.{u} A] [Category.{u} B] (F : A ⥤ B), W F → W' F

/-- The argument of Proposition 4 for (ii) ⇒ (iii), with the inclusion
`W ⊆ W₀` it needs made a hypothesis. -/
theorem proposition4_ii_iii {W : ClasseDeFoncteurs.{u}} (hW : Inclus W W₀)
    (A : Type u) [Category.{u} A] (h : TotalementAspherique W A) : ConditionIII A := by
  sorry

end Grothendieck.Folder114
