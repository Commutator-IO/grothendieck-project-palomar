module

public import Mathlib
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Grothendieck.Upstream.KaroubiAdditiveFunctors

@[expose] public section


/-!
# Folder 113, page 3: the Karoubi envelope and Morita invariance (partial)

The modernised reading `transcripts/113/113.modern.tex`, page 3, states for a
small `k`-additive category `P`, with `P^k = Hom_k(P°, Ab_k)`:

> Le plongement de Yoneda `P ↪ P^k` est additif et pleinement fidèle, et il
> induit `Kar(P) ⥲ Proj_tf(P^k)`, `(Kar P)^k ⥲ P^k`, où `Proj_tf(P^k)` est la
> sous-catégorie pleine des objets projectifs de type fini : les facteurs
> directs des objets représentables. C'est l'invariance de Morita.

and it notes that `P^k` does not depend on the `k`-structure: an additive
functor `P° → Ab` is automatically `k`-module valued.

What is formalised.

* `enveloppe_libre`: the Karoubi envelope is the free completion under
  retracts — restriction along `P → Kar P` is an equivalence
  `Fun(Kar P, D) ≌ Fun(P, D)` for every idempotent-complete `D`. **This is in
  mathlib** (`CategoryTheory.Idempotents.karoubiUniversal`, Joël Riou); the
  file only restates it.
* `morita`: the second equivalence of the reading, `(Kar P)^k ≃ P^k`, in the
  form: restriction along `P° → (Kar P)°` is an equivalence from additive
  functors `(Kar P)° → D` to additive functors `P° → D`, for any preadditive
  idempotent-complete `D` — in particular `D = ModuleCat k` (`morita_module`).
  The additive form is the one the reading's remark licenses; the `k`-linear
  form (and the remark itself) is not formalised. The ingredients not in
  mathlib are proved here: `Kar(P°) ≌ (Kar P)°` compatibly with the embeddings
  (`opKaroubi`, `toKaroubi_op_eq`), and the fact that a functor on
  `(Kar P)°` is additive as soon as its restriction to `P°` is
  (`additive_of_toKaroubi_op`).

Not formalised: `Kar(P) ≃ Proj_tf(P^k)`, which needs the projective objects of
a functor category (mathlib has no theory of projective generators of
`Fun(P°, Ab)`); nor the reading's recognition theorem (Freyd–Mitchell).

What the formalisation found: nothing wrong in the part formalised. The
smallness of `P` and abelianness of the target are not used — only that the
target is preadditive and idempotent complete.
-/

namespace Grothendieck.Folder113

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Idempotents.Karoubi
  CategoryTheory.Limits Opposite

universe v u v' u'

variable (P : Type u) [Category.{v} P]

/-- **Free completion under retracts** (in mathlib). Restriction along
`P → Kar P` is an equivalence `Fun(Kar P, D) ≌ Fun(P, D)` for `D` idempotent
complete. -/
theorem enveloppe_libre (D : Type u') [Category.{v'} D] [IsIdempotentComplete D] :
    ((Functor.whiskeringLeft P (Karoubi P) D).obj (toKaroubi P)).IsEquivalence :=
  inferInstance

/-- `Kar(P°) → (Kar P)°`. -/
@[simps]
def opKaroubi : Karoubi Pᵒᵖ ⥤ (Karoubi P)ᵒᵖ where
  obj Q := op ⟨Q.X.unop, Q.p.unop, by rw [← unop_comp, Q.idem]⟩
  map f := op ⟨f.f.unop, by dsimp; rw [← unop_comp, ← unop_comp, Category.assoc, f.comm]⟩
  map_id Q := by apply Quiver.Hom.unop_inj; ext; rfl
  map_comp f g := by apply Quiver.Hom.unop_inj; ext; rfl

/-- `Kar(P°) → (Kar P)°` is an equivalence (indeed an isomorphism of
categories): faithful, full, and every object is hit on the nose. -/
instance : (opKaroubi P).IsEquivalence where
  faithful := ⟨fun {Q₁ Q₂} f g h => by
    ext
    exact congrArg (fun k => k.unop.f) h⟩
  full := ⟨fun {Q₁ Q₂} g => by
    refine ⟨⟨(g.unop.f : Q₂.X.unop ⟶ Q₁.X.unop).op, ?_⟩, rfl⟩
    apply Quiver.Hom.unop_inj
    show (Q₂.p.unop ≫ (g.unop.f : Q₂.X.unop ⟶ Q₁.X.unop)) ≫ Q₁.p.unop = g.unop.f
    exact (Category.assoc _ _ _).trans g.unop.comm⟩
  essSurj := ⟨fun Q => ⟨⟨op Q.unop.X, Q.unop.p.op, by rw [← op_comp, Q.unop.idem]⟩,
    ⟨Iso.refl _⟩⟩⟩

/-- The two embeddings agree: `P° → Kar(P°) → (Kar P)°` is `(P → Kar P)°`. -/
theorem toKaroubi_op_eq : (toKaroubi P).op = toKaroubi Pᵒᵖ ⋙ opKaroubi P := rfl

variable (D : Type u') [Category.{v'} D]

/-- Restriction along `P° → (Kar P)°` is an equivalence `Fun((Kar P)°, D) ≌
Fun(P°, D)` for `D` idempotent complete. -/
instance restriction_isEquivalence [IsIdempotentComplete D] :
    ((Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op).IsEquivalence := by
  rw [toKaroubi_op_eq]
  exact inferInstanceAs ((Functor.whiskeringLeft _ _ D).obj (opKaroubi P) ⋙
    (Functor.whiskeringLeft _ _ D).obj (toKaroubi Pᵒᵖ)).IsEquivalence

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
    (restrictionAdditive P (ModuleCat.{u'} k)).IsEquivalence :=
  inferInstance

end Grothendieck.Folder113
