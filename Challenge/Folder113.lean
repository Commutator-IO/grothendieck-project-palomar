module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Challenge.Upstream.KaroubiAdditiveFunctors

@[expose] public section

namespace Grothendieck.Folder113

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Idempotents.Karoubi CategoryTheory.Limits Opposite

universe v u v' u'

variable (P : Type u) [Category.{v} P]

variable (D : Type u') [Category.{v'} D]

variable [Preadditive P] [Preadditive D]

/-- A functor on `(Kar P)°` is additive as soon as its restriction to `P°` is. -/
theorem additive_of_toKaroubi_op (F : (Karoubi P)ᵒᵖ ⥤ D)
    [((toKaroubi P).op ⋙ F).Additive] : F.Additive where
  map_add {Q₁ Q₂ f g} := by
    have key : ∀ h : Q₁ ⟶ Q₂, F.map h = F.map (decompId_p Q₁.unop).op ≫
        ((toKaroubi P).op ⋙ F).map h.unop.f.op ≫ F.map (decompId_i Q₂.unop).op := by
      intro h
      conv_lhs => rw [← Quiver.Hom.op_unop h, Karoubi.hom_eq_decompId_i_comp h.unop]
      rw [op_comp, op_comp, F.map_comp, F.map_comp, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op, Category.assoc]
    rw [key, key f, key g, unop_add, show (f.unop + g.unop).f = f.unop.f + g.unop.f from rfl,
      op_add, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The restriction functor on additive functors. -/
def restrictionAdditive : ((Karoubi P)ᵒᵖ ⥤+ D) ⥤ (Pᵒᵖ ⥤+ D) :=
  (additiveFunctor Pᵒᵖ D).lift
    (AdditiveFunctor.forget _ _ ⋙ (Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op)
    (fun F => by
      change ((toKaroubi P).op ⋙ F.obj).Additive
      infer_instance)

/-- **Morita invariance**, `(Kar P)^k ≃ P^k` in its additive form: restriction
along `P° → (Kar P)°` is an equivalence from additive functors `(Kar P)° → D`
to additive functors `P° → D`, for `D` preadditive and idempotent complete. -/
instance morita [IsIdempotentComplete D] : (restrictionAdditive P D).IsEquivalence := by
  let W := (Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op
  have hW : W.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful W
  have hff : (restrictionAdditive P D).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := AdditiveFunctor.forget _ _)
      ((ObjectProperty.fullyFaithfulι _).comp hW)
  have : (restrictionAdditive P D).Full := hff.full
  have : (restrictionAdditive P D).Faithful := hff.faithful
  have : (restrictionAdditive P D).EssSurj := ⟨fun G => by
    let F := W.objPreimage G.obj
    let e : W.obj F ≅ G.obj := W.objObjPreimageIso G.obj
    have : ((toKaroubi P).op ⋙ F).Additive := Functor.additive_of_iso e.symm
    have : F.Additive := additive_of_toKaroubi_op P D F
    exact ⟨⟨F, this⟩, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  exact { }

/-- The case of modules: `(Kar P)^k ≃ P^k` with values in `k`-modules. -/
theorem morita_module (k : Type u') [CommRing k] :
    (restrictionAdditive P (ModuleCat.{u'} k)).IsEquivalence := by
  sorry

end Grothendieck.Folder113
