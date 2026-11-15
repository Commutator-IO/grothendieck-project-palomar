module

public import Mathlib
public import Grothendieck.Folder19
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

@[expose] public section


/-!
# Folder 19, after théorème 1.12: descent along a surjective morphism of topoi

The edition's reading of théorème 1.12 (`docs/lean/sections/19.tex`) applies it to topoi: for
a morphism of topoi `u : E → F` whose inverse image `u*` is conservative, `u*` is left adjoint
to `u_*`, conservative and left exact, hence commutes with all equalizers, and théorème 1.12
in the margin's form identifies `F` with the category of coalgebras of the comonad `u* u_*` on
`E`. The section notes that this application was not formalised, Mathlib having no morphisms
of topoi.

This file states it with the structure `MorphismOfTopoi` of the vendored AxiomMath/Stacks
library (file `StacksFrontier/CategoryTheory/Sites/Topos/MorphismOfTopoi.lean`: a pushforward,
an inverse image, the adjunction, and left exactness of the inverse image), and with the
morphism of topoi of a morphism of sites, `Functor.IsMorphismOfSites.morphismOfTopoi`
(Stacks tag 00XC, same file; `IsMorphismOfSites` is in
`StacksFrontier/CategoryTheory/Sites/MorphismOfSites.lean`). The proof is
`Grothendieck.Folder19.theoreme_b_suffisance` (Beck's theorem through condition C) applied to
the adjunction `u* ⊣ u_*`: condition C holds because the target has equalizers and the inverse
image preserves finite limits, equalizers among them.

**What is proved.**
* `conditionC_inverseImage`: for a morphism of topoi whose target has equalizers, the inverse
  image satisfies condition C of page 4;
* `MorphismOfTopoi.comparison_isEquivalence` (the remark): if moreover the inverse image is
  conservative, the comparison functor from the target `F` to the coalgebras of the comonad
  `u* u_*` on the source `E` is an equivalence;
* `IsMorphismOfSites.comparison_isEquivalence`: the same for the morphism of topoi
  `Sh(D) → Sh(C)` of a morphism of sites given by `u : C ⥤ D` with `u_s` conservative:
  `Sh(C)` is equivalent to the coalgebras of `u_s u^s` on `Sh(D)`.

The hypothesis is the conservativity of `u*`; the identification with surjective morphisms
(`u*` faithful) and the criterion of page 34 of folder 161-2 are not formalised here.
-/

namespace Grothendieck.Folder19

open CategoryTheory Limits

universe v u u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v} F]

/-- The inverse image of a morphism of topoi whose target has equalizers satisfies
condition C: equalizers exist in the target, and the inverse image, being left exact,
commutes with them. -/
theorem conditionC_inverseImage (φ : MorphismOfTopoi E F) [HasEqualizers F] :
    ConditionC φ.inverseImage := by
  intro X Y a b _
  have := φ.preservesFiniteLimits
  exact ⟨inferInstance, inferInstance⟩

/-- **The remark after théorème 1.12.** For a morphism of topoi `φ : E → F` whose target has
equalizers and whose inverse image `φ*` is conservative, `F` is equivalent, by the comparison
functor, to the category of coalgebras of the comonad `φ* φ_*` on `E`. -/
theorem MorphismOfTopoi.comparison_isEquivalence (φ : MorphismOfTopoi E F) [HasEqualizers F]
    [φ.inverseImage.ReflectsIsomorphisms] :
    (Comonad.comparison φ.adj).IsEquivalence :=
  theoreme_b_suffisance φ.adj (conditionC_inverseImage φ)

/-- **The same for a morphism of sites** (Stacks 00XC): for `u : C ⥤ D` a morphism of sites
`(D, K) → (C, J)` whose pullback `u_s : Sh(C) ⥤ Sh(D)` is conservative, `Sh(C)` is equivalent to
the category of coalgebras of the comonad `u_s u^s` on `Sh(D)`. -/
theorem IsMorphismOfSites.comparison_isEquivalence {C D : Type u} [SmallCategory C]
    [SmallCategory D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    (h : u.IsMorphismOfSites J K) [h.morphismOfTopoi.inverseImage.ReflectsIsomorphisms] :
    (Comonad.comparison h.morphismOfTopoi.adj).IsEquivalence :=
  MorphismOfTopoi.comparison_isEquivalence h.morphismOfTopoi

end Grothendieck.Folder19
