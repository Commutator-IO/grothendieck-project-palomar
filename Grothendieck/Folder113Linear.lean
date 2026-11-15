module

public import Mathlib
public import Grothendieck.Folder113
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Category

@[expose] public section


/-!
# Folder 113, page 3: Morita invariance in its `k`-linear form

`Grothendieck/Folder113.lean` proves Morita invariance `(Kar P)^k ≃ P^k` in its additive form
(`morita`: restriction along `P° → (Kar P)°` is an equivalence on additive functors) and leaves
out the `k`-linear form, for want of a `k`-linear structure on the Karoubi envelope in Mathlib.

That structure is `CategoryTheory.Idempotents.Karoubi.linear` (with `Karoubi.instModule`) of the
vendored AxiomMath/Stacks file
`StacksFrontier/AlgebraicGeometry/WeilCohomology/Motives/Category.lean`, the file of the
category of Chow motives (Stacks tag 0FGA): `r • f` on `Hom((X, p), (Y, q))` is `r • f` in `P`,
which the idempotents absorb. Upstream it is a `local instance`; this file switches it on with
`attribute [local instance]`, so that it is in force only here.

**What is proved.** Let `k` be a commutative ring, `P` a `k`-linear category and `D` a
`k`-linear category.
* `linear_of_toKaroubi_op`: a functor on `(Kar P)°` is `k`-linear as soon as its
  restriction to `P°` is (the `k`-linear analogue of `additive_of_toKaroubi_op`);
* `linearFunctor`, `restrictionLinear`: the full subcategory of additive `k`-linear functors and
  the restriction functor between them;
* `morita_linear` (**Morita invariance, `k`-linear form**): for `D` idempotent complete,
  restriction along `P° → (Kar P)°` is an equivalence from additive `k`-linear functors
  `(Kar P)° → D` to additive `k`-linear functors `P° → D`;
* `morita_linear_module`: the case `D = ModuleCat k`, the reading's `(Kar P)^k ≃ P^k` with
  `P^k` the `k`-linear presheaves of `k`-modules.

Not formalised: the reading's remark that an additive functor `P° → Ab` is automatically
`k`-module valued (so that `P^k` does not depend on the `k`-structure), and
`Kar(P) ≃ Proj_tf(P^k)`.
-/

namespace Grothendieck.Folder113

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Idempotents.Karoubi
  CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.Idempotents.Karoubi.linear

universe v u v' u' w

variable (k : Type w) [CommRing k] (P : Type u) [Category.{v} P] [Preadditive P] [Linear k P]
  (D : Type u') [Category.{v'} D] [Preadditive D] [Linear k D]

/-- A functor on `(Kar P)°` is `k`-linear as soon as its restriction to `P°` is. -/
theorem linear_of_toKaroubi_op (F : (Karoubi P)ᵒᵖ ⥤ D)
    [((toKaroubi P).op ⋙ F).Linear k] : F.Linear k where
  map_smul {Q₁ Q₂} f r := by
    have key : ∀ h : Q₁ ⟶ Q₂, F.map h = F.map (decompId_p Q₁.unop).op ≫
        ((toKaroubi P).op ⋙ F).map h.unop.f.op ≫ F.map (decompId_i Q₂.unop).op := by
      intro h
      conv_lhs => rw [← Quiver.Hom.op_unop h, Karoubi.hom_eq_decompId_i_comp h.unop]
      rw [op_comp, op_comp, F.map_comp, F.map_comp, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op, Category.assoc]
    rw [key, key f, Linear.unop_smul, smul_f, Linear.op_smul, Functor.map_smul, Linear.smul_comp,
      Linear.comp_smul]

/-- Additive `k`-linear functors, as a property of objects of `C ⥤ D`. -/
def linearFunctor (C : Type*) [Category C] [Preadditive C] [Linear k C] :
    ObjectProperty (C ⥤ D) :=
  fun F => F.Additive ∧ F.Linear k

/-- The restriction functor on additive `k`-linear functors, along `P° → (Kar P)°`. -/
def restrictionLinear :
    (linearFunctor k D (Karoubi P)ᵒᵖ).FullSubcategory ⥤
      (linearFunctor k D Pᵒᵖ).FullSubcategory :=
  (linearFunctor k D Pᵒᵖ).lift
    ((linearFunctor k D (Karoubi P)ᵒᵖ).ι ⋙
      (Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op)
    (fun F => by
      obtain ⟨_, _⟩ := F.property
      change ((toKaroubi P).op ⋙ F.obj).Additive ∧ ((toKaroubi P).op ⋙ F.obj).Linear k
      refine ⟨inferInstance, ⟨fun f r => ?_⟩⟩
      change F.obj.map ((toKaroubi P).map (r • f).unop).op =
        r • F.obj.map ((toKaroubi P).map f.unop).op
      rw [show ((toKaroubi P).map (r • f).unop).op = r • ((toKaroubi P).map f.unop).op from rfl,
        Functor.map_smul])

/-- **Morita invariance, `k`-linear form.** For `D` a `k`-linear idempotent-complete category,
restriction along `P° → (Kar P)°` is an equivalence from additive `k`-linear functors
`(Kar P)° → D` to additive `k`-linear functors `P° → D`. -/
instance morita_linear [IsIdempotentComplete D] : (restrictionLinear k P D).IsEquivalence := by
  let W := (Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op
  have hW : W.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful W
  have hff : (restrictionLinear k P D).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
      ((ObjectProperty.fullyFaithfulι _).comp hW)
  have : (restrictionLinear k P D).Full := hff.full
  have : (restrictionLinear k P D).Faithful := hff.faithful
  have : (restrictionLinear k P D).EssSurj := ⟨fun G => by
    obtain ⟨_, _⟩ := G.property
    let F := W.objPreimage G.obj
    let e : W.obj F ≅ G.obj := W.objObjPreimageIso G.obj
    have : ((toKaroubi P).op ⋙ F).Additive := Functor.additive_of_iso e.symm
    have : F.Additive := additive_of_toKaroubi_op P D F
    have : ((toKaroubi P).op ⋙ F).Linear k := Functor.linear_of_iso k e.symm
    have : F.Linear k := linear_of_toKaroubi_op k P D F
    exact ⟨⟨F, ⟨inferInstance, inferInstance⟩⟩, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  exact { }

/-- The case of modules: `(Kar P)^k ≃ P^k` for `k`-linear presheaves of `k`-modules. -/
theorem morita_linear_module :
    (restrictionLinear k P (ModuleCat.{w} k)).IsEquivalence :=
  inferInstance

end Grothendieck.Folder113
