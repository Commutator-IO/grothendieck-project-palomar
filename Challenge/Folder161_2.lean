module

public import Mathlib.CategoryTheory.Monad.Monadicity
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Limits.Indization.Category

@[expose] public section

namespace Grothendieck.Folder161_2

open CategoryTheory Limits

section GabrielUlmer

universe w v u

variable (C : Type u) [Category.{v} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]

/-- **Page 61, Corollaire.** « Une `𝒰`-catégorie cocomplète `E` est équivalente à
un `Ind_π(𝒞)`, `𝒞` petite, si et seulement si elle admet une petite
sous-catégorie strictement génératrice formée d'objets accessibles. »

In current terms: a cocomplete, locally small category is locally presentable
iff it has a small full subcategory which is dense (« strictement génératrice »:
every object is the canonical colimit over `𝒞/X`) and made of presentable
(« accessibles ») objects. mathlib's `IsLocallyPresentable` stands for the left
side: cocomplete, with a small family of `κ`-presentable objects of which every
object is a `κ`-filtered colimit — i.e. `E ≃ Ind_κ(𝒞)`. -/
theorem caracterisation_gabriel_ulmer :
    IsLocallyPresentable.{w} C ↔
      ∃ P : ObjectProperty C, ObjectProperty.Small.{w} P ∧ P.ι.IsDense ∧
        ∀ X, P X → IsPresentable.{w} X := by
  sorry

end GabrielUlmer

end Grothendieck.Folder161_2
