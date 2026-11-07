module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section

namespace Grothendieck.Folder113

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Idempotents.Karoubi CategoryTheory.Limits Opposite

universe v u v' u'

variable (P : Type u) [Category.{v} P]

variable (D : Type u') [Category.{v'} D]

variable [Preadditive P] [Preadditive D]

/-- The restriction functor on additive functors. -/
def restrictionAdditive : ((Karoubi P)ᵒᵖ ⥤+ D) ⥤ (Pᵒᵖ ⥤+ D) :=
  (additiveFunctor Pᵒᵖ D).lift
    (AdditiveFunctor.forget _ _ ⋙ (Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op)
    (fun F => by
      change ((toKaroubi P).op ⋙ F.obj).Additive
      infer_instance)

/-- The case of modules: `(Kar P)^k ≃ P^k` with values in `k`-modules. -/
theorem morita_module (k : Type u') [CommRing k] :
    (restrictionAdditive P (ModuleCat.{u'} k)).IsEquivalence := by
  sorry

end Grothendieck.Folder113
