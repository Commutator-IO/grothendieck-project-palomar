module

public import Mathlib.CategoryTheory.Monad.Monadicity
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Limits.Indization.Category

public section


/-!
# Folder 161-2: Lawvere theories, monadicity, and locally presentable categories

Issue #26 lists folder 161-2 in tier 2: « Lawvere theories and locally
presentable categories; partial support only ». What of that row the reading
`transcripts/161-2/161-2.modern.tex` states crisply is formalised here, and
nothing else of the folder.

* **Pages 33–34, the working sheets on Lawvere theories.** They carry two
  statements. `monadicite`: « un foncteur `U : A → B` admettant un adjoint à
  gauche `F` est monadique si `U` est conservatif et si `A` a et `U` préserve
  les coégalisateurs des paires réflexives » — Beck's crude monadicity theorem,
  in mathlib (`Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms`).
  `descente`: for a morphism of topoi `f`, the comparison functor `B' → B_π`
  into the coalgebras of `π = f^* f_*` is an equivalence as soon as `f^*` is
  conservative, « la seconde condition du critère … étant acquise parce que
  `f^*` est exact à gauche ». Proved for any adjunction `f^* ⊣ f_*` with `f^*`
  left exact and conservative out of a category with finite limits — the topos
  structure is not used — from mathlib's coreflexive comonadicity theorem.
* **Page 61, Corollaire** (`caracterisation_gabriel_ulmer`): « une
  `𝒰`-catégorie cocomplète `E` est équivalente à un `Ind_π(𝒞)`, `𝒞` petite, si
  et seulement si elle admet une petite sous-catégorie strictement génératrice
  formée d'objets accessibles ». « Strictement génératrice » is taken as the
  reading's page-56 definition, i.e. *dense* (mathlib `Functor.IsDense`), and
  « accessible » as *presentable* (the reading's footnote). The left side is
  mathlib's `IsLocallyPresentable` (cocomplete, and every object a `κ`-filtered
  colimit of a small family of `κ`-presentable objects, which is what
  `E ≃ Ind_κ(𝒞)` says; the literal `Ind_π(𝒞)` of SGA 4 is not in mathlib). The
  proof glues mathlib's Adámek–Rosický 1.20
  (`IsCardinalLocallyPresentable.iff_exists_isStrongGenerator`), density of the
  presentable objects, and a bound on a small family of cardinals.
* **Page 77, Lemme** (`lemme_ind`), the finite-limit case of the duality: for a
  small `Σ` with finite colimits, the ind-objects of `Σ` are exactly the
  left-exact presheaves, so `Ind(Σ) ≃ Hom_lex(Σ°, Ens)`. In mathlib
  (`isIndObject_iff_preservesFiniteLimits`).

**What the formalisation finds.** Nothing false, and no missing hypothesis: all
four statements hold as the reading gives them, and all four rest on results
already in mathlib (the Gabriel–Ulmer corollary needing a short argument to
pass from mathlib's strong-generator form to the reading's dense-subcategory
form). The descent criterion is more general than stated: no topos is needed.

**Not formalised** from the row: the page-33 adjunction between the models of a
Lawvere theory `Hom'(𝓛°, ENS)` and the algebras of a monad (the page gives no
statement precise enough); the page-54 theorem (`π`-accessible ⟺ `Ind_π(𝒞)` ⟺
`E_π` small and strictly generating), the page-55 corollary and the claim that
`(Ens)°`, `(Ab)°` are not accessible, the page-56 list on strictly generating
functors, the page-59 lemma on `Ind_π(𝒞)` and cardinal filtrations (mathlib has
no `Ind_π`), and the page-77 corollary (a model is representable iff
`Hom_S(X, -)` commutes with filtered colimits).

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder161_2

open CategoryTheory Limits

section Monadicite

universe v u₁ u₂

variable {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]

/-- **Page 33, the monadicity theorem.** « Un foncteur `U : A → B` admettant un
adjoint à gauche `F` est monadique (`A ≃ Alg(T)`, `T = UF`) si `U` est
conservatif et si `A` a et `U` préserve les coégalisateurs des paires
réflexives. » -/
theorem monadicite {F : B ⥤ A} {U : A ⥤ B} (adj : F ⊣ U) [HasReflexiveCoequalizers A]
    [U.ReflectsIsomorphisms]
    (hU : ∀ ⦃X Y : A⦄ (f g : X ⟶ Y), IsReflexivePair f g → PreservesColimit (parallelPair f g) U) :
    (Monad.comparison adj).IsEquivalence := by
  have : Monad.PreservesColimitOfIsReflexivePair U := ⟨fun _ _ f g _ => hU f g inferInstance⟩
  exact (Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms adj).eqv

/-- **Page 34, the descent criterion.** For `f^* ⊣ f_*` with `f^*` left exact and
conservative, the comparison functor `B' → B_π`, `π = f^* f_*`, into the
coalgebras of the comonad `π` is an equivalence. The page states it for a
morphism of topoi; only finite limits in `B'` are used. -/
theorem descente {fStar : B ⥤ A} {fLower : A ⥤ B} (adj : fStar ⊣ fLower) [HasFiniteLimits B]
    [PreservesFiniteLimits fStar] [fStar.ReflectsIsomorphisms] :
    (Comonad.comparison adj).IsEquivalence := by
  have : Comonad.PreservesLimitOfIsCoreflexivePair fStar := ⟨fun _ _ _ _ _ => inferInstance⟩
  exact (Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms adj).eqv

end Monadicite

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
  constructor
  · intro _
    obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
    let P := isCardinalPresentable C κ
    obtain ⟨Q, _, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} P
    refine ⟨Q, inferInstance, ?_, fun X hX => ?_⟩
    · have : (ObjectProperty.ιOfLE hQP).EssSurj := ⟨fun Y => by
        obtain ⟨Z, hZ, ⟨e⟩⟩ := hPQ _ Y.2
        exact ⟨⟨Z, hZ⟩, ⟨P.isoMk e.symm⟩⟩⟩
      have : (ObjectProperty.ιOfLE hQP).IsEquivalence := { }
      rw [Functor.IsDense.iff_of_iso (ObjectProperty.ιOfLECompιIso hQP).symm,
        Functor.IsDense.comp_left_iff_of_isEquivalence]
      infer_instance
    · have : IsCardinalPresentable X κ := hQP _ hX
      exact isPresentable_of_isCardinalPresentable X κ
  · rintro ⟨P, _, _, hP⟩
    choose κ hκ hX using fun x : Subtype P => (hP x.1 x.2).exists_cardinal
    obtain ⟨c, hc⟩ := Cardinal.bddAbove_of_small (s := Set.range κ)
    let κ₀ : Cardinal.{w} := Order.succ (max c Cardinal.aleph0)
    have : Fact κ₀.IsRegular := ⟨Cardinal.isRegular_succ (le_max_right _ _)⟩
    refine ⟨κ₀, this, ?_⟩
    rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
    refine ⟨P, inferInstance, ?_, fun X hX' => ?_⟩
    · have h := Functor.isStrongGenerator_of_isDense P.ι
      convert h
      ext X
      simp only [ObjectProperty.ofObj_iff, ObjectProperty.ι_obj]
      exact ⟨fun h => ⟨⟨X, h⟩, rfl⟩, fun ⟨Y, hY⟩ => hY ▸ Y.2⟩
    · have := hX ⟨X, hX'⟩
      have hle : κ ⟨X, hX'⟩ ≤ κ₀ :=
        (hc ⟨_, rfl⟩).trans ((le_max_left _ _).trans (Order.le_succ _))
      rw [isCardinalPresentable_iff]
      exact isCardinalPresentable_of_le X hle

end GabrielUlmer

section LimitesFinies

universe u

/-- **Page 77, Lemme** (finite-limit theories). For `R` small with finite limits,
`S = Hom_lex(R, Ens)` and `Σ = R° ⊂ S` the representable models: « le foncteur
d'inclusion `Σ → S` induit une équivalence `Ind(Σ) ≃ S` ». Stated with `Σ`
itself (a small category with finite colimits, `R = Σ°`), so that `S` is the
category of left-exact presheaves on `Σ`: the ind-objects of `Σ` are exactly the
left-exact presheaves (mathlib's `isIndObject_iff_preservesFiniteLimits`), whence
`Ind(Σ) ≃ S` as full subcategories of `Σ̂`. -/
theorem lemme_ind (Sig : Type u) [SmallCategory Sig] [HasFiniteColimits Sig] :
    (IsIndObject (C := Sig)) = (fun A : Sigᵒᵖ ⥤ Type u => PreservesFiniteLimits A) ∧
      Nonempty (Ind Sig ≌
        ObjectProperty.FullSubcategory (fun A : Sigᵒᵖ ⥤ Type u => PreservesFiniteLimits A)) := by
  have h : (IsIndObject (C := Sig)) = (fun A : Sigᵒᵖ ⥤ Type u => PreservesFiniteLimits A) :=
    funext fun A => propext (isIndObject_iff_preservesFiniteLimits A)
  exact ⟨h, ⟨h ▸ Ind.equivalence Sig⟩⟩

end LimitesFinies

end Grothendieck.Folder161_2
