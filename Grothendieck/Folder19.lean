module

public import Mathlib
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Limits.Pi
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.Order.Sum.Order

@[expose] public section


/-!
# Folder 19: the comonadicity theorem (page 4), the comonad over a product base
# (pages 7–11), Gabriel–Popescu (pages 14–15) and chains of adjoints (pages 79–80)

Issue #26 lists folder 19 in tier 2: « Comonadicity and Gabriel–Popescu ». Those
two statements of `transcripts/19/19.modern.tex` are formalised here, and the
finding `19-comonad-matrix-product-base` (pages 7–11).

## Théorème 1.12 (page 4)

> **Théorème.** Soit `f ⊣ g` une adjonction, `φ = fg`, et `h` le foncteur de
> comparaison.
> a) Si les noyaux de doubles flèches existent dans `A` et si `f` y commute,
>    alors `h` est essentiellement surjectif.
> b) `h` est une équivalence si et seulement si `f` est conservatif et si, pour
>    toute double flèche `(u,v)` de `A` telle que `Ker(f(u), f(v))` existe,
>    `Ker(u,v)` existe et `f` y commute.
>
> La restriction portée en marge — il suffit de considérer les doubles flèches
> `(u,v)` dont l'image par `f` a un noyau — est la condition que le manuscrit
> appelle *condition C*. [Footnote:] Les doubles flèches dont `f` voit le noyau
> sont, dans le vocabulaire d'aujourd'hui, les paires `f`-scindées.

`h` is mathlib's `Comonad.comparison adj`, and condition C is `ConditionC` below.

* `theoreme_a` — a), in the margin's weaker form (condition C instead of all
  equalizers), and `theoreme_a'` in the form of the text. True as stated.
* `theoreme_b_suffisance` — the « il suffit » of b). True as stated; it is an
  application of mathlib's Beck theorem
  `Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`.
* `theoreme_b_necessite_fausse` — **the « il faut » of b) is false.** A
  comonadic `f` need not satisfy condition C. Counterexample, with `B = Bool → Type`
  (pairs of sets `(X, Y)`) and `A` the full subcategory of pairs with
  `Y ≠ ∅ ⇒ X ≠ ∅`: the inclusion `f` is coreflective (right adjoint
  `(X, Y) ↦ (X, Y if X ≠ ∅ else ∅)`), hence comonadic; but the pair
  `(*, *) ⇉ (Bool, *)` given by `x ↦ true` and `x ↦ false` has equalizer `(∅, *)`
  in `B`, which is not in `A`, so `f` does not commute with the equalizer taken
  in `A` (which is `(∅, ∅)`).
* `beck_iff` — the correct statement: `h` is an equivalence iff `f` is
  conservative and, for every **`f`-split** pair (one whose image has a *split*
  equalizer), `Ker(u,v)` exists and `f` commutes with it. From mathlib.

So the reading faithfully reproduces the manuscript (the transcription, page 4,
has « il faut et il suffit » and the margin's condition C), and the footnote's
gloss is where the error sits: a pair « dont `f` voit le noyau » is not an
`f`-split pair. Every `f`-split pair has an equalizer in `B`, so condition C is
*stronger* than Beck's condition: sufficient, not necessary. The same applies
to the « Conclusion » of pages 4–6 (adjunctions with `f` conservative and
condition C ↔ comonads): the comonads so obtained are only those whose forgetful
functor satisfies condition C, and the counterexample above is one that does not;
with Beck's condition in place of C the correspondence is right.

## A product base: the matrix of the `φ_ji` (pages 7–11)

> Le reste du texte examine ce que devient tout ceci quand `B = ∏_{i ∈ I} B_i`. […]
> En posant `φ_ji = f_j g_i : B_i → B_j` et en supposant que les `f_j` commutent
> aux produits indexés par `I` — ce qui est automatique si `I` est fini, ou si les
> `f_j` sont exacts — on obtient `pr_j φ((X_i)) = ∏_i φ_ji(X_i)`. […] une famille
> `λ_kji : φ_ki → φ_kj φ_ji`, obtenue en insérant l'unité `id → g_j f_j` au milieu.
> […] pour `i = j = k` on retrouve la comultiplication de `φ_i`, et les cas où
> deux des trois indices coïncident sont dégénérés. […] Deux facteurs, `g'`, `g''`
> pleinement fidèles : deux foncteurs croisés `φ' : B'' → B'`, `φ'' : B' → B''`,
> deux flèches `λ' : id → φ'φ''`, `λ'' : id → φ''φ'`, avec
> `φ(X', X'') = (X' × φ'(X''), φ''(X') × X'')`.

Setting: adjunctions `f_i ⊣ g_i`, `f_i : A → B_i`, and `A` with `I`-indexed products.
* `adjPi` — (3.4): `f = (f_i) ⊣ g`, `g((X_i)) = ∏ g_i(X_i)`.
* `matrice` — (3.6): if `f_j` commutes with `I`-indexed products, `pr_j φ((X_i))` is
  the product of the `φ_ji(X_i)`, with projections `f_j(pr_i)`. True as stated.
* `counit_matrice`, `comult_matrice` — (3.9): `ᾱ_k = α_k(X_k) ∘ pr_k` and
  `λ̄_kji = λ_kji(X_i) ∘ pr_i`; no hypothesis needed. `comult_unique`: under the
  hypothesis of `matrice`, these entries determine the comultiplication.
* `lam_diag` — the margin of page 8: `λ_iii` is the comultiplication of `φ_i`.
* `lam_isIso_left`, `lam_isIso_right` — the degenerate cases: if the `g` are fully
  faithful, `λ_kki` and `λ_kjj` are isomorphisms.
* `lamUnit`, `lam_eq_counit_comp_lamUnit` — (3.11 b), (3.14): `λ_iji` is the unit
  `λ' : id → φ_ij φ_ji` after the isomorphism `φ_ii ≅ id`.
* `deuxFacteurs_left`, `deuxFacteurs_right` — (3.12)–(3.14) for `I = WalkingPair`:
  `pr' φ(X', X'') = X' × φ'(X'')` and `pr'' φ(X', X'') = φ''(X') × X''`.
* `matrice_fini_fausse` — **« ou I fini » is false**: a left adjoint need not
  commute with finite products. With `I = Bool`, `A = B_i = Type`,
  `f_i = Bool × -` (left adjoint to `Bool → -`), `X_i = *`: `pr_j φ(X)` has two
  elements and `∏_i φ_ji(X_i)` four. The phrase is on the page (« p. ex. `f_j`
  exacts ; ou `I` fini », transcription page 7); the exactness alternative is right.

The coassociativity relations between the `λ_kji`, which the page does not write,
and the description of `A` by quadruples `(X', X'', u', u'')` (pages 9–10), are not
formalised.

## Gabriel–Popescu (pages 14–15)

> Le foncteur `Hom_C(U, -) : C → Mod_R` est pleinement fidèle, et son adjoint à
> gauche `- ⊗_R U` est exact : c'est le théorème de Gabriel–Popescu.

(`C` a Grothendieck category, `U` a generator, `R = End_C(U)`, modules on the
right.) This is in mathlib (`IsGrothendieckAbelian.GabrielPopescu.full`,
`…preservesFiniteLimits`, and `isSeparator_iff_faithful_preadditiveCoyonedaObj`);
`gabriel_popescu` restates it in the reading's form. A generator is mathlib's
*separator*, and right `R`-modules are `ModuleCat Rᵐᵒᵖ`. The reading's further
claim — the functor is an equivalence iff `U` is moreover small projective
(Morita) — and the manuscript's original claim of an equivalence for a bare
generator are not formalised here.

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder19

open CategoryTheory Limits

universe w v u₁ u₂

section Comonadicite

variable {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
variable {f : A ⥤ B} {g : B ⥤ A} (adj : f ⊣ g)

/-- **Condition C** (margin of page 4): for every pair `(u, v)` of `A` such that
`Ker(f u, f v)` exists, `Ker(u, v)` exists and `f` commutes with it. -/
def ConditionC (f : A ⥤ B) : Prop :=
  ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), HasEqualizer (f.map u) (f.map v) →
    HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f

open Comonad ComonadicityInternal in
/-- **Théorème 1.12 a)**, in the margin's form: under condition C the comparison
functor `h : A → φ-Coalg` is essentially surjective. -/
theorem theoreme_a (hC : ConditionC f) : (Comonad.comparison adj).EssSurj := by
  have hE : ∀ X : adj.toComonad.Coalgebra,
      HasEqualizer (g.map X.a) (adj.unit.app (g.obj X.A)) := fun X =>
    (hC _ _ inferInstance).1
  have hP : ∀ X : adj.toComonad.Coalgebra,
      PreservesLimit (parallelPair (g.map X.a) (adj.unit.app (g.obj X.A))) f := fun X =>
    (hC _ _ inferInstance).2
  have : ∀ X : Coalgebra adj.toComonad, IsIso ((comparisonAdjunction adj).counit.app X) := by
    intro X
    apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
    change IsIso ((comparisonAdjunction adj).counit.app X).f
    rw [comparisonAdjunction_counit_f]
    change IsIso (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
      (counitLimitOfPreservesEqualizer X)).inv
    exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv
  exact ⟨fun X => ⟨_, ⟨asIso ((comparisonAdjunction adj).counit.app X)⟩⟩⟩

/-- **Théorème 1.12 a)**, as the text states it: if the equalizers of pairs exist
in `A` and `f` commutes with them, `h` is essentially surjective. -/
theorem theoreme_a' [HasEqualizers A] [PreservesLimitsOfShape WalkingParallelPair f] :
    (Comonad.comparison adj).EssSurj :=
  theoreme_a adj fun _ _ _ _ _ => ⟨inferInstance, inferInstance⟩

/-- **Théorème 1.12 b), sufficiency.** If `f` is conservative and satisfies
condition C, the comparison functor is an equivalence. -/
theorem theoreme_b_suffisance [f.ReflectsIsomorphisms] (hC : ConditionC f) :
    (Comonad.comparison adj).IsEquivalence := by
  have : Comonad.HasEqualizerOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).1⟩
  have : Comonad.PreservesLimitOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).2⟩
  exact (Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj).eqv

/-- **Beck's theorem, precise form** (the necessary and sufficient condition the
reading's b) should carry): the comparison functor is an equivalence iff `f` is
conservative and, for every `f`-split pair `(u, v)` — one whose image has a
*split* equalizer — `Ker(u, v)` exists and `f` commutes with it. -/
theorem beck_iff : (Comonad.comparison adj).IsEquivalence ↔
    f.ReflectsIsomorphisms ∧ ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), f.IsCosplitPair u v →
      HasEqualizer u v ∧ PreservesLimit (parallelPair u v) f := by
  constructor
  · intro h
    let _ : ComonadicLeftAdjoint f := ⟨g, adj, h⟩
    refine ⟨⟨fun {X Y} φ hφ => ?_⟩, fun X Y u v _ => ?_⟩
    · have : IsIso ((Comonad.comparison adj).map φ) := by
        have : IsIso ((Comonad.forget adj.toComonad).map ((Comonad.comparison adj).map φ)) := hφ
        exact isIso_of_reflects_iso _ (Comonad.forget adj.toComonad)
      exact isIso_of_fully_faithful (Comonad.comparison adj) φ
    have := Comonad.createsFSplitEqualizersOfComonadic (F := f) u v
    have : HasLimit (parallelPair u v ⋙ f) := by
      rw [hasLimit_iff_of_iso (diagramIsoParallelPair _)]
      exact inferInstanceAs <| HasEqualizer (f.map u) (f.map v)
    exact ⟨hasLimit_of_created (parallelPair u v) f, inferInstance⟩
  · rintro ⟨_, hC⟩
    have : Comonad.HasEqualizerOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).1⟩
    have : Comonad.PreservesLimitOfIsCosplitPair f := ⟨fun u v _ => (hC u v inferInstance).2⟩
    exact (Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms adj).eqv

end Comonadicite

section ContreExemple

/-- An object `(X, Y)` of `Bool → Type`: `X` at `true`, `Y` at `false`. -/
def mkObj (X Y : Type) : Bool → Type
  | true => X
  | false => Y

/-- Pairs `(X, Y)` with `Y → Nonempty X`: if `Y` is inhabited, so is `X`. -/
def P : ObjectProperty (Bool → Type) := fun Z => Z false → Nonempty (Z true)

/-- The coreflection `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def Robj (Z : Bool → Type) : P.FullSubcategory :=
  ⟨mkObj (Z true) {_y : Z false // Nonempty (Z true)}, fun y => y.2⟩

/-- The hom-set bijection of the coreflection. -/
def e (X : P.FullSubcategory) (Z : Bool → Type) : (P.ι.obj X ⟶ Z) ≃ (X ⟶ Robj Z) where
  toFun φ := P.homMk fun b => match b with
    | true => φ true
    | false => TypeCat.ofHom fun q => ⟨φ false q, (X.property q).map (φ true)⟩
  invFun ψ := fun b => match b with
    | true => ψ.hom true
    | false => ψ.hom false ≫ TypeCat.ofHom Subtype.val
  left_inv φ := by
    funext b; cases b <;> rfl
  right_inv ψ := by
    apply ObjectProperty.hom_ext; funext b; cases b <;> rfl

/-- `P ↪ (Bool → Type)` is left adjoint to `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def adjP : P.ι ⊣ Adjunction.rightAdjointOfEquiv e (by
    intro X' X Y f g; apply ObjectProperty.hom_ext; funext b; cases b <;> rfl) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The inclusion of `P` is coreflective. -/
instance : Coreflective P.ι where
  R := _
  adj := adjP

/-- The inclusion `P ↪ (Bool → Type)` is comonadic (it is coreflective). -/
theorem comonadique : (Comonad.comparison adjP).IsEquivalence :=
  (comonadicOfCoreflective (R := P.ι)).eqv

/-- `(*, *)` -/
def S0 : P.FullSubcategory := ⟨mkObj PUnit PUnit, fun _ => ⟨PUnit.unit⟩⟩
/-- `(Bool, *)` -/
def T0 : P.FullSubcategory := ⟨mkObj Bool PUnit, fun _ => ⟨true⟩⟩
/-- `((↦ true), id)` -/
def u0 : S0 ⟶ T0 := P.homMk fun b => match b with
  | true => TypeCat.ofHom fun _ => true
  | false => 𝟙 _
/-- `((↦ false), id)` -/
def v0 : S0 ⟶ T0 := P.homMk fun b => match b with
  | true => TypeCat.ofHom fun _ => false
  | false => 𝟙 _

/-- The inclusion `P ↪ (Bool → Type)` does **not** satisfy condition C: for
`u, v : (*, *) ⇉ (Bool, *)`, `(u, v) = ((↦ true), id), ((↦ false), id)`, the
equalizer of `f u, f v` in `Bool → Type` is `(∅, *)`; an equalizer in `P`, if
`f` commuted with it, would have `*` on its `false` side, hence (being in `P`) a
point on its `true` side — which `u` and `v` send to `true ≠ false`. -/
theorem non_conditionC : ¬ ConditionC P.ι := by
  intro hC
  have : HasEqualizer (P.ι.map u0) (P.ι.map v0) := pi.hasLimit_of_hasLimit_comp_eval
  obtain ⟨_, _⟩ := hC u0 v0 this
  -- the fork `(∅, *) → (*, *)` of `Bool → Type`
  let K : Fork (P.ι.map u0) (P.ι.map v0) := Fork.ofι (P := mkObj PEmpty PUnit)
    (fun b => match b with
      | true => TypeCat.ofHom PEmpty.elim
      | false => 𝟙 _) (by
        funext b; cases b
        · rfl
        · ext x; cases x)
  let l := (isLimitOfHasEqualizerOfPreservesLimit P.ι u0 v0).lift K
  obtain ⟨x⟩ := (equalizer u0 v0).property (l false PUnit.unit)
  have h := congrArg (fun φ : equalizer u0 v0 ⟶ T0 => (φ.hom true) x) (equalizer.condition u0 v0)
  exact Bool.noConfusion (h : true = false)

/-- **Théorème 1.12 b), necessity: false as stated.** Here is an adjunction
`f ⊣ g` whose comparison functor is an equivalence, and yet `f` does not satisfy
condition C. The correct necessary condition is the one of `beck_iff`, on
`f`-split pairs only. -/
theorem theoreme_b_necessite_fausse :
    (Comonad.comparison adjP).IsEquivalence ∧ ¬ ConditionC P.ι :=
  ⟨comonadique, non_conditionC⟩

end ContreExemple

section GabrielPopescu

/-- **Pages 14–15, as corrected by the reading.** Let `C` be a Grothendieck
category with a generator `U` (mathlib: a *separator*), `R = End(U)`. Then
`Hom_C(U, -) : C → Mod_R` (right `R`-modules, i.e. modules over `Rᵐᵒᵖ`) is fully
faithful, and its left adjoint `- ⊗_R U` is exact. This is mathlib's
Gabriel–Popescu theorem. -/
theorem gabriel_popescu {C : Type u₁} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] (U : C) (hU : IsSeparator U) :
    (preadditiveCoyonedaObj U).Full ∧ (preadditiveCoyonedaObj U).Faithful ∧
      PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj U) ∧
      PreservesFiniteColimits (IsGrothendieckAbelian.tensorObj U) :=
  ⟨IsGrothendieckAbelian.GabrielPopescu.full U hU,
    (isSeparator_iff_faithful_preadditiveCoyonedaObj U).1 hU,
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits U hU, inferInstance⟩

end GabrielPopescu

section BaseProduit

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂} [∀ i, Category.{v} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- (3.4) The right adjoint over the product base, `g((Xᵢ)) = ∏ᵢ gᵢ(Xᵢ)`. -/
noncomputable abbrev gPi [HasProductsOfShape I A] : (∀ i, B i) ⥤ A where
  obj X := ∏ᶜ fun i => (g i).obj (X i)
  map φ := Limits.Pi.map fun i => (g i).map (φ i)

variable [HasProductsOfShape I A]

/-- (3.4) `f = (fᵢ) : A → ∏ Bᵢ` is left adjoint to `g = ∏ gᵢ`. -/
noncomputable def adjPi : Functor.pi' f ⊣ gPi g := Adjunction.mkOfHomEquiv
  { homEquiv := fun Y X =>
      { toFun := fun φ => Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)
        invFun := fun ψ i => ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
        left_inv := fun φ => by
          funext i
          simp only [Limits.Pi.lift_comp_π]
          exact Equiv.symm_apply_apply _ _
        right_inv := fun ψ => by
          refine Limits.Pi.hom_ext _ _ fun i => ?_
          simp only [Limits.Pi.lift_comp_π]
          exact Equiv.apply_symm_apply _ _ }
    homEquiv_naturality_left_symm := fun h ψ => by
      funext i
      change ((adj i).homEquiv _ _).symm ((h ≫ ψ) ≫ Limits.Pi.π _ i) =
        (f i).map h ≫ ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
      rw [Category.assoc]
      exact (adj i).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := fun φ ψ => by
      refine Limits.Pi.hom_ext _ _ fun i => ?_
      change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ ((φ ≫ ψ) i)) ≫ Limits.Pi.π _ i =
        ((Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)) ≫
          Limits.Pi.map (fun i => (g i).map (ψ i))) ≫ Limits.Pi.π _ i
      rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc]
      exact (adj i).homEquiv_naturality_right _ _ }

@[reassoc (attr := simp)]
theorem adjPi_unit_π (Y : A) (j : I) :
    (adjPi f g adj).unit.app Y ≫ Limits.Pi.π _ j = (adj j).unit.app Y := by
  change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ (𝟙 ((f i).obj Y))) ≫ Limits.Pi.π _ j = _
  rw [Limits.Pi.lift_comp_π]
  exact (adj j).homEquiv_id Y

theorem adjPi_counit (X : ∀ i, B i) (j : I) :
    (adjPi f g adj).counit.app X j =
      (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫ (adj j).counit.app (X j) := by
  change ((adj j).homEquiv ((gPi g).obj X) (X j)).symm
    (𝟙 ((gPi g).obj X) ≫ Limits.Pi.π (fun i => (g i).obj (X i)) j) = _
  rw [Category.id_comp]
  exact (adj j).homEquiv_counit _ _ _

/-- (3.6) The entry `φ_ji = f_j g_i : B_i → B_j` of the matrix. -/
abbrev phi (j i : I) : B i ⥤ B j := g i ⋙ f j

/-- (3.10) `λ_kji : φ_ki → φ_kj φ_ji`, the unit `id → g_j f_j` inserted in the middle of
`f_k g_i`. -/
@[simps]
def lam (k j i : I) : phi f g k i ⟶ phi f g j i ⋙ phi f g k j where
  app X := (f k).map ((adj j).unit.app ((g i).obj X))
  naturality X Y h := by
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
    exact congrArg (f k).map ((adj j).unit.naturality ((g i).map h))

/-- (3.5)–(3.6) **The matrix.** If `f_j` commutes with `I`-indexed products, the
`j`-th component of `φ((Xᵢ))` is the product of the `φ_ji(Xᵢ)`, with projections
`f_j(prᵢ)`. -/
noncomputable def matrice (X : ∀ i, B i) (j : I) [PreservesLimitsOfShape (Discrete I) (f j)] :
    IsLimit (Fan.mk ((adjPi f g adj).toComonad.obj X j)
      fun i => (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)) :=
  (isLimitMapConeFanMkEquiv (f j) _ _) (isLimitOfPreserves (f j) (productIsProduct _))

/-- (3.9), first line: the counit of `φ` is diagonal, `ᾱ_k = α_k(X_k) ∘ pr_k`. -/
theorem counit_matrice (X : ∀ i, B i) (k : I) :
    (adjPi f g adj).toComonad.ε.app X k =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) k) ≫ (adj k).counit.app (X k) :=
  adjPi_counit f g adj X k

/-- (3.9), second line: the `(k, j, i)` entry of the comultiplication of `φ` is
`λ̄_kji = λ_kji(Xᵢ) ∘ prᵢ`. -/
theorem comult_matrice (X : ∀ i, B i) (k j i : I) :
    (adjPi f g adj).toComonad.δ.app X k ≫
        (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i))) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (lam f g adj k j i).app (X i) := by
  have h1 := adjPi_unit_π_assoc f g adj ((gPi g).obj X) j
    ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))
  have h2 := (adj j).unit.naturality (Limits.Pi.π (fun i => (g i).obj (X i)) i)
  have h3 := congrArg (f k).map (h1.trans h2.symm)
  exact (((f k).map_comp _ _).symm.trans h3).trans ((f k).map_comp _ _)

/-- **The comultiplication is the family `λ_kji`.** If the `f_j` commute with
`I`-indexed products, a morphism `(φX)_k → (φ²X)_k` with the entries `λ̄_kji` of
`comult_matrice` is the `k`-th component of the comultiplication. -/
theorem comult_unique [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] (X : ∀ i, B i) (k : I)
    (t : (adjPi f g adj).toComonad.obj X k ⟶
      ((adjPi f g adj).toComonad.obj ((adjPi f g adj).toComonad.obj X)) k)
    (ht : ∀ j i, t ≫
        (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i))) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (lam f g adj k j i).app (X i)) :
    t = (adjPi f g adj).toComonad.δ.app X k := by
  have hk := (isLimitMapConeFanMkEquiv (f k) _ _)
    (isLimitOfPreserves (f k) (productIsProduct
      (fun j => (g j).obj ((f j).obj ((gPi g).obj X)))))
  refine Fan.IsLimit.hom_ext hk _ _ fun j => ?_
  have : PreservesLimitsOfShape (Discrete I) (g j) := (adj j).rightAdjoint_preservesLimits.1
  have hj := (isLimitMapConeFanMkEquiv (f j ⋙ g j ⋙ f k) _ _)
    (isLimitOfPreserves (f j ⋙ g j ⋙ f k) (productIsProduct (fun i => (g i).obj (X i))))
  refine Fan.IsLimit.hom_ext hj _ _ fun i => ?_
  have e := (ht j i).trans (comult_matrice f g adj X k j i).symm
  have e' : t ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) =
      (adjPi f g adj).toComonad.δ.app X k ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) :=
    (congrArg (t ≫ ·) ((f k).map_comp _ _).symm).trans
      (e.trans (congrArg (_ ≫ ·) ((f k).map_comp _ _)))
  exact (Category.assoc _ _ _).trans (e'.trans (Category.assoc _ _ _).symm)

omit [HasProductsOfShape I A] in
/-- Marginal note of page 8: for `i = j = k`, `λ_kji` is the comultiplication `λ_i`
of the comonad `φ_i = f_i g_i`. -/
theorem lam_diag (i : I) : lam f g adj i i i = (adj i).toComonad.δ := by
  ext X
  rfl

section PleinementFideles

omit [HasProductsOfShape I A] in
/-- If `g_i` is fully faithful, the diagonal entry `φ_ii = f_i g_i` is the identity
(through the counit). -/
noncomputable def diagIso (i : I) [(g i).Full] [(g i).Faithful] : phi f g i i ≅ 𝟭 (B i) :=
  asIso (adj i).counit

omit [HasProductsOfShape I A] in
/-- Pages 8–9, the degenerate cases `k = j`: if `g_k` is fully faithful,
`λ_kki : φ_ki → φ_kk φ_ki` is an isomorphism. -/
theorem lam_isIso_left (k i : I) [(g k).Full] [(g k).Faithful] :
    IsIso (lam f g adj k k i) := by
  have : ∀ X, IsIso ((lam f g adj k k i).app X) := fun X =>
    NatIso.isIso_app_of_isIso (Functor.whiskerRight (adj k).unit (f k)) ((g i).obj X)
  exact NatIso.isIso_of_isIso_app _

omit [HasProductsOfShape I A] in
/-- Pages 8–9, the degenerate cases `j = i`: if `g_j` is fully faithful,
`λ_kjj : φ_kj → φ_kj φ_jj` is an isomorphism. -/
theorem lam_isIso_right (k j : I) [(g j).Full] [(g j).Faithful] :
    IsIso (lam f g adj k j j) := by
  have : ∀ X, IsIso ((lam f g adj k j j).app X) := fun X => by
    have := NatIso.isIso_app_of_isIso (Functor.whiskerLeft (g j) (adj j).unit) X
    exact Functor.map_isIso (f k) ((adj j).unit.app ((g j).obj X))
  exact NatIso.isIso_of_isIso_app _

omit [HasProductsOfShape I A] in
/-- (3.11 b), (3.14) The unit `λ' : id_{B_i} → φ_ij φ_ji` (`i ≠ j`) when `g_i` is
fully faithful: `λ_iji` read through `φ_ii ≅ id`. -/
noncomputable def lamUnit (i j : I) [(g i).Full] [(g i).Faithful] :
    𝟭 (B i) ⟶ phi f g j i ⋙ phi f g i j :=
  (diagIso f g adj i).inv ≫ lam f g adj i j i

omit [HasProductsOfShape I A] in
/-- `λ_iji = λ' ∘ α_i`: the entry `(i, j, i)` is the unit `λ'` after the counit
`φ_ii → id`. -/
theorem lam_eq_counit_comp_lamUnit (i j : I) [(g i).Full] [(g i).Faithful] :
    lam f g adj i j i = (adj i).counit ≫ lamUnit f g adj i j := by
  simp [lamUnit, diagIso]

end PleinementFideles

end BaseProduit

section DeuxFacteurs

variable {C : Type u₁} [Category.{v} C]

/-- The family `(a, b)` on the two indices of `WalkingPair`. -/
def famPair {F : WalkingPair → C} {T : C} (a : T ⟶ F .left) (b : T ⟶ F .right) :
    ∀ j, T ⟶ F j
  | .left => a
  | .right => b

/-- A fan over `WalkingPair` that is a limit, with its first leg corrected by an
isomorphism, is a binary product. -/
def binaryFanOfFanLeft {F : WalkingPair → C} {P : C} (p : ∀ j, P ⟶ F j)
    (h : IsLimit (Fan.mk P p)) {Y : C} (e : F .left ≅ Y) :
    IsLimit (BinaryFan.mk (p .left ≫ e.hom) (p .right)) :=
  BinaryFan.IsLimit.mk _
    (fun {T} a b => (Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) : T ⟶ P))
    (fun {T} a b => show Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p .left ≫ e.hom = a by
      have h1 : Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p .left = a ≫ e.inv :=
        Fan.IsLimit.fac h _ .left
      rw [reassoc_of% h1]; simp)
    (fun {T} a b => show Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p .right = b from
      Fan.IsLimit.fac h _ .right)
    (fun {T} a b (m : T ⟶ P) (ha : m ≫ p .left ≫ e.hom = a) (hb : m ≫ p .right = b) => by
      refine Fan.IsLimit.hom_ext h _ _ fun j => ?_
      show m ≫ p j = Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p j
      have h1 : Fan.IsLimit.lift h (famPair (a ≫ e.inv) b) ≫ p j = famPair (a ≫ e.inv) b j :=
        Fan.IsLimit.fac h _ j
      rw [h1]
      cases j
      · simp [famPair, ← ha]
      · simpa [famPair] using hb)

/-- The same, with the second leg corrected. -/
def binaryFanOfFanRight {F : WalkingPair → C} {P : C} (p : ∀ j, P ⟶ F j)
    (h : IsLimit (Fan.mk P p)) {Y : C} (e : F .right ≅ Y) :
    IsLimit (BinaryFan.mk (p .left) (p .right ≫ e.hom)) :=
  BinaryFan.IsLimit.mk _
    (fun {T} a b => (Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) : T ⟶ P))
    (fun {T} a b => show Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p .left = a from
      Fan.IsLimit.fac h _ .left)
    (fun {T} a b => show Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p .right ≫ e.hom = b by
      have h1 : Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p .right = b ≫ e.inv :=
        Fan.IsLimit.fac h _ .right
      rw [reassoc_of% h1]; simp)
    (fun {T} a b (m : T ⟶ P) (ha : m ≫ p .left = a) (hb : m ≫ p .right ≫ e.hom = b) => by
      refine Fan.IsLimit.hom_ext h _ _ fun j => ?_
      show m ≫ p j = Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p j
      have h1 : Fan.IsLimit.lift h (famPair a (b ≫ e.inv)) ≫ p j = famPair a (b ≫ e.inv) j :=
        Fan.IsLimit.fac h _ j
      rw [h1]
      cases j
      · simpa [famPair] using ha
      · simp [famPair, ← hb])

variable {A : Type u₁} [Category.{v} A] {B : WalkingPair → Type u₂} [∀ i, Category.{v} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)
variable [HasProductsOfShape WalkingPair A]

/-- (3.12)–(3.14), first factor. With `g'` fully faithful and `f'` commuting with
binary products, `pr' φ(X', X'') = X' × φ'(X'')`, `φ' = f' g''`. -/
noncomputable def deuxFacteurs_left (X : ∀ i, B i) [(g .left).Full] [(g .left).Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) (f .left)] :
    IsLimit (BinaryFan.mk
      ((f .left).map (Limits.Pi.π (fun i => (g i).obj (X i)) .left) ≫
        (adj .left).counit.app (X .left))
      ((f .left).map (Limits.Pi.π (fun i => (g i).obj (X i)) .right) :
        (adjPi f g adj).toComonad.obj X .left ⟶ (phi f g .left .right).obj (X .right))) :=
  binaryFanOfFanLeft _ (matrice f g adj X .left) (asIso ((adj .left).counit.app (X .left)))

/-- (3.12)–(3.14), second factor: `pr'' φ(X', X'') = φ''(X') × X''`, `φ'' = f'' g'`. -/
noncomputable def deuxFacteurs_right (X : ∀ i, B i) [(g .right).Full] [(g .right).Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) (f .right)] :
    IsLimit (BinaryFan.mk
      ((f .right).map (Limits.Pi.π (fun i => (g i).obj (X i)) .left) :
        (adjPi f g adj).toComonad.obj X .right ⟶ (phi f g .right .left).obj (X .left))
      ((f .right).map (Limits.Pi.π (fun i => (g i).obj (X i)) .right) ≫
        (adj .right).counit.app (X .right))) :=
  binaryFanOfFanRight _ (matrice f g adj X .right) (asIso ((adj .right).counit.app (X .right)))

end DeuxFacteurs

section ContreExempleFini

/-- `Y ↦ Bool × Y`. -/
def Fb : Type ⥤ Type where
  obj Y := Bool × Y
  map h := TypeCat.ofHom (Prod.map id h)

/-- `X ↦ (Bool → X)`. -/
def Gb : Type ⥤ Type where
  obj X := Bool → X
  map h := TypeCat.ofHom fun u b => h (u b)

/-- `Bool × - ⊣ (Bool → -)`. -/
def adjB : Fb ⊣ Gb := Adjunction.mkOfHomEquiv
  { homEquiv := fun _ _ =>
      { toFun := fun φ => TypeCat.ofHom fun y b => φ (b, y)
        invFun := fun ψ => TypeCat.ofHom fun p => ψ p.2 p.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

/-- **Page 7, « ou I fini »: false.** With `I = Bool`, `A = B_i = Set` and
`f_i = Bool × -` (left adjoint of `Bool → -`), `pr_j φ((Xᵢ))` is not a product of the
`φ_ji(Xᵢ)`: for `Xᵢ = *` the first has two elements, the second four. The finite
products of `I` are not automatically preserved by the left adjoints `f_j`. -/
theorem matrice_fini_fausse :
    ¬ Nonempty ((adjPi (B := fun _ : Bool => Type) (fun _ => Fb) (fun _ => Gb)
        (fun _ => adjB)).toComonad.obj (fun _ => PUnit) true ≅
      ∏ᶜ fun i : Bool => (phi (B := fun _ : Bool => Type) (fun _ => Fb) (fun _ => Gb)
        true i).obj PUnit) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  have h1 : Nat.card ((adjPi (B := fun _ : Bool => Type) (fun _ => Fb) (fun _ => Gb)
      (fun _ => adjB)).toComonad.obj (fun _ => PUnit) true) = 2 := by
    change Nat.card (Bool × ∏ᶜ fun _ : Bool => (Bool → PUnit)) = 2
    rw [Nat.card_prod, Nat.card_congr (Types.productIso _).toEquiv]
    simp
  have h2 : Nat.card (∏ᶜ fun i : Bool => (phi (B := fun _ : Bool => Type) (fun _ => Fb)
      (fun _ => Gb) true i).obj PUnit) = 4 := by
    change Nat.card (∏ᶜ fun _ : Bool => Bool × (Bool → PUnit)) = 4
    rw [Nat.card_congr (Types.productIso _).toEquiv]
    simp
  omega

end ContreExempleFini

section ChainesAdjoints

/-!
## Pages 79–80: chains of adjoints between presheaf topoi

The Proposition of page 80: for every `n`, `n` successive adjoint functors between presheaf
topoi on small categories, none fully faithful. The construction gives more: a chain infinite
in both directions on the presheaves on `ℤ ⊕ ℤ`, which answers the page's Question.

* `preAdj`: an adjunction `u ⊣ v` between small categories gives `u^* ⊣ v^*` on presheaves.
* `not_faithful`: for preorders and `u : C ⥤ D`, if some `q ≰ p` has
  `u c ≤ q → u c ≤ p` for every `c`, the restriction `u^*` is not faithful.
* `Bmap k`: on `ℤ`, `e m x = 2x + m` and `r m x = ⌊(x - m)/2⌋` satisfy `e m ⊣ r m ⊣ e (m+1)`;
  on `ℤ ⊕ ℤ` the maps `Bmap (2m) = e m ⊕ r m`, `Bmap (2m+1) = r m ⊕ e (m+1)` satisfy
  `Bmap k ⊣ Bmap (k+1)` for every `k ∈ ℤ` (`gc`).
* `chain_adj`, `chain_not_faithful`: the restrictions `F k = (Bmap k)^*` satisfy
  `F k ⊣ F (k+1)` for all `k ∈ ℤ`, and none is faithful, hence none fully faithful.
* `proposition_page80`: the Proposition, for every `n`.
-/

open CategoryTheory

/-- Restriction along `u`, on presheaves of sets. -/
abbrev pre {C D : Type} [Category C] [Category D] (u : C ⥤ D) :
    (Dᵒᵖ ⥤ Type) ⥤ (Cᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ Type).obj u.op

/-- An adjunction `u ⊣ v` gives `u^* ⊣ v^*` on presheaves. -/
def preAdj {C D : Type} [Category C] [Category D] {u : C ⥤ D} {v : D ⥤ C} (adj : u ⊣ v) :
    pre u ⊣ pre v :=
  (Adjunction.op adj).whiskerLeft _

variable {C D : Type} [Preorder C] [Preorder D]

open Classical in
/-- The presheaf `x ↦ {b : Bool // x ≤ p → b = false}`. -/
noncomputable def sep (p : D) : Dᵒᵖ ⥤ Type where
  obj x := {b : Bool // x.unop ≤ p → b = false}
  map {_ y} _ := TypeCat.ofHom fun b =>
    ⟨if y.unop ≤ p then false else b.1, fun h => by simp [h]⟩
  map_id x := ConcreteCategory.hom_ext _ _ fun b => Subtype.ext (by
    by_cases h : x.unop ≤ p
    · simp [h, b.2 h]
    · simp [h])
  map_comp {x y z} f g := ConcreteCategory.hom_ext _ _ fun b => Subtype.ext (by
    have hzy := leOfHom g.unop
    by_cases hz : z.unop ≤ p
    · simp [hz]
    · have : ¬ y.unop ≤ p := fun h => hz (hzy.trans h)
      simp [hz, this])

/-- The presheaf represented by `q`. -/
def rep (q : D) : Dᵒᵖ ⥤ Type where
  obj x := PLift (x.unop ≤ q)
  map f := TypeCat.ofHom fun h => ⟨(leOfHom f.unop).trans h.down⟩

open Classical in
/-- The two maps `rep q ⟶ sep p`, by the value `b` at `q`. -/
noncomputable def arrow (q p : D) (b : Bool) : rep q ⟶ sep p where
  app x := TypeCat.ofHom fun _ =>
    ⟨if x.unop ≤ p then false else b, fun h' => by simp [h']⟩
  naturality x y f := ConcreteCategory.hom_ext _ _ fun h => Subtype.ext (by
    have hyx := leOfHom f.unop
    by_cases hy : y.unop ≤ p
    · simp [rep, sep, hy]; rfl
    · have : ¬ x.unop ≤ p := fun h => hy (hyx.trans h)
      simp [rep, sep, hy, this]; rfl)

open Classical in
/-- If every `u c` below `q` is below `p` and `q ≰ p`, restriction along `u` is not
faithful. -/
theorem not_faithful (u : C ⥤ D) (q p : D) (hqp : ¬ q ≤ p)
    (h : ∀ c, u.obj c ≤ q → u.obj c ≤ p) : ¬ (pre u).Faithful := by
  intro hf
  have heq : (pre u).map (arrow q p true) = (pre u).map (arrow q p false) := by
    refine NatTrans.ext (funext fun c => ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_)
    change (if u.obj c.unop ≤ p then false else true) =
      (if u.obj c.unop ≤ p then false else false)
    simp only [h c.unop x.down, ↓reduceIte]
  have h2 := congrArg (fun α : rep q ⟶ sep p =>
    (α.app (Opposite.op q) (PLift.up (le_refl q) : PLift (q ≤ q))).1) ((pre u).map_injective heq)
  change (if q ≤ p then false else true) = (if q ≤ p then false else false) at h2
  simp only [hqp, ↓reduceIte, Bool.true_eq_false] at h2

/-- The maps of the chain on `ℤ ⊕ ℤ`. -/
def Bmap (k : ℤ) : ℤ ⊕ ℤ → ℤ ⊕ ℤ :=
  if k % 2 = 0 then Sum.map (fun x => 2 * x + k / 2) (fun x => (x - k / 2) / 2)
  else Sum.map (fun x => (x - k / 2) / 2) (fun x => 2 * x + (k / 2 + 1))

/-- `Bmap k ⊣ Bmap (k + 1)` for every `k ∈ ℤ`. -/
theorem gc (k : ℤ) : GaloisConnection (Bmap k) (Bmap (k + 1)) := by
  intro x y
  unfold Bmap
  by_cases hk : k % 2 = 0
  · simp only [hk, show ¬ (k + 1) % 2 = 0 by omega, show (k + 1) / 2 = k / 2 by omega, ↓reduceIte]
    rcases x with x | x <;> rcases y with y | y <;> simp <;> omega
  · simp only [hk, show (k + 1) % 2 = 0 by omega, show (k + 1) / 2 = k / 2 + 1 by omega,
      ↓reduceIte]
    rcases x with x | x <;> rcases y with y | y <;> simp <;> omega

/-- The functor of `Bmap k` on the poset `ℤ ⊕ ℤ`. -/
def chainFun (k : ℤ) : (ℤ ⊕ ℤ) ⥤ (ℤ ⊕ ℤ) := (gc k).monotone_l.functor

/-- The `k`-th functor of the chain, restriction along `Bmap k`. -/
abbrev chain (k : ℤ) : ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) := pre (chainFun k)

/-- **Infinite in both directions**: `chain k ⊣ chain (k + 1)` for every `k ∈ ℤ`. -/
def chainAdj (k : ℤ) : chain k ⊣ chain (k + 1) := preAdj (gc k).adjunction

theorem chain_adj (k : ℤ) : Nonempty (chain k ⊣ chain (k + 1)) := ⟨chainAdj k⟩

/-- No functor of the chain is faithful. -/
theorem chain_not_faithful (k : ℤ) : ¬ (chain k).Faithful := by
  by_cases hk : k % 2 = 0
  · refine not_faithful (chainFun k) (Sum.inl (k / 2 + 1)) (Sum.inl (k / 2))
      (by simp only [Sum.inl_le_inl_iff]; omega) ?_
    intro c hc
    change Bmap k c ≤ _ at hc
    change Bmap k c ≤ _
    simp only [Bmap, hk, ↓reduceIte] at hc ⊢
    rcases c with x | x
    · simp only [Sum.map_inl, Sum.inl_le_inl_iff] at hc ⊢; omega
    · simp at hc
  · refine not_faithful (chainFun k) (Sum.inr (k / 2 + 2)) (Sum.inr (k / 2 + 1))
      (by simp only [Sum.inr_le_inr_iff]; omega) ?_
    intro c hc
    change Bmap k c ≤ _ at hc
    change Bmap k c ≤ _
    simp only [Bmap, hk, ↓reduceIte] at hc ⊢
    rcases c with x | x
    · simp at hc
    · simp only [Sum.map_inr, Sum.inr_le_inr_iff] at hc ⊢; omega

theorem chain_not_fullyFaithful (k : ℤ) : ¬ ((chain k).Full ∧ (chain k).Faithful) :=
  fun h => chain_not_faithful k h.2

/-- **Page 80, Proposition.** For every `n`, `n` functors between presheaf topoi on a small
category, each right adjoint to the previous, none fully faithful. -/
theorem proposition_page80 (n : ℕ) :
    ∃ G : Fin n → (((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type) ⥤ ((ℤ ⊕ ℤ)ᵒᵖ ⥤ Type)),
      (∀ (i : Fin n) (h : i.1 + 1 < n), Nonempty (G i ⊣ G ⟨i.1 + 1, h⟩)) ∧
      ∀ i, ¬ ((G i).Full ∧ (G i).Faithful) := by
  refine ⟨fun i => chain i.1, fun i _ => ?_, fun i => chain_not_fullyFaithful _⟩
  have := chain_adj (i.1 : ℤ)
  rwa [show ((i.1 : ℤ) + 1) = ((i.1 + 1 : ℕ) : ℤ) by push_cast; rfl] at this

end ChainesAdjoints

/-!
## The relations between the `λ_kji` and the quadruples (pages 7–11, continued)

This completes the finding `19-comonad-matrix-product-base` (issue #89, row 53); the
module docstring above, written before, lists these two points as not formalised.

* `lam_counit_right`, `lam_counit_left`, `lam_coassoc` — the counit and coassociativity
  relations of the matrix `(φ_ji, α_i, λ_kji)`, which the page declines to write:
  `φ_ki(α_i) ∘ λ_kii = id`, `α_k φ_ki ∘ λ_kki = id`, and
  `φ_lk(λ_kji) ∘ λ_lki = λ_lkj φ_ji ∘ λ_lji`. No hypothesis.
* `counit_iff`, `coassoc_iff`, `hom_iff` — a morphism `a : X → φX` with entries
  `u_ki = f_k(prᵢ) ∘ a_k : X_k → φ_ki(X_i)` is a coalgebra iff `α_k ∘ u_kk = id` and
  `λ_kji ∘ u_ki = φ_kj(u_ji) ∘ u_kj`; morphisms likewise. The coassociativity and the
  morphisms need the `f_j` to commute with `I`-indexed products; the counit does not.
* `Quadruplet`, `versQuadruplets`, `versQuadruplets_isEquivalence` — two factors, `g'`,
  `g''` fully faithful, `f'`, `f''` commuting with binary products: the coalgebras of `φ`
  are the quadruples `(X', X'', u', u'')` with the two triangles of pages 9–10.
  Of the eight coassociativity relations, the two with `k = i ≠ j` are the triangles and
  the six others hold automatically (`rel_right`, `rel_left`, `rel_unit`).
* `quadruplets` — if moreover `f = (f', f'')` is comonadic, `A` is equivalent to the
  category of quadruples, `Y ↦ (f'Y, f''Y, f'(η''_Y), f''(η'_Y))`.
-/

section MatriceRelations

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂}
  [∀ i, Category.{v} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- Right counit relation: `φ_ki(α_i) ∘ λ_kii = id`. -/
theorem lam_counit_right (k i : I) (X : B i) :
    (lam f g adj k i i).app X ≫ (phi f g k i).map ((adj i).counit.app X) = 𝟙 _ := by
  simp only [lam_app, Functor.comp_map, ← Functor.map_comp, Adjunction.right_triangle_components]
  exact (f k).map_id _

/-- Left counit relation: `α_k φ_ki ∘ λ_kki = id`. -/
theorem lam_counit_left (k i : I) (X : B i) :
    (lam f g adj k k i).app X ≫ (adj k).counit.app ((phi f g k i).obj X) = 𝟙 _ := by
  simp only [lam_app]
  exact (adj k).left_triangle_components _

/-- **Coassociativity of the matrix**: `φ_lk(λ_kji) ∘ λ_lki = λ_lkj φ_ji ∘ λ_lji`,
both being `f_l(η_k) ∘ f_l(η_j)` in different orders (naturality of `η_k`). -/
theorem lam_coassoc (l k j i : I) (X : B i) :
    (lam f g adj l k i).app X ≫ (phi f g l k).map ((lam f g adj k j i).app X) =
      (lam f g adj l j i).app X ≫ (lam f g adj l k j).app ((phi f g j i).obj X) := by
  simp only [lam_app, Functor.comp_map, Functor.comp_obj, ← Functor.map_comp]
  congr 1
  exact ((adj k).unit.naturality _).symm

/-- `l ≫ e = 𝟙` and `e ≫ i = 𝟙` give `l = i`. -/
theorem eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} (l : X ⟶ Y) (e : Y ⟶ X)
    (i : X ⟶ Y) (h1 : l ≫ e = 𝟙 X) (h2 : e ≫ i = 𝟙 Y) : l = i := by
  rw [← Category.comp_id l, ← h2, ← Category.assoc, h1, Category.id_comp]

/-- With `g_i` fully faithful, `λ_kii = φ_ki(α_i⁻¹)`. -/
theorem lam_app_right (k i : I) [(g i).Full] [(g i).Faithful] (X : B i) :
    (lam f g adj k i i).app X = (phi f g k i).map ((diagIso f g adj i).inv.app X) :=
  eq_of_comp_eq_id _ ((phi f g k i).map ((adj i).counit.app X)) _ (lam_counit_right f g adj k i X)
    (((phi f g k i).map_comp _ _).symm.trans
      ((congrArg (phi f g k i).map ((diagIso f g adj i).hom_inv_id_app X)).trans
        ((phi f g k i).map_id _)))

/-- With `g_k` fully faithful, `λ_kki = α_k⁻¹ φ_ki`. -/
theorem lam_app_left (k i : I) [(g k).Full] [(g k).Faithful] (X : B i) :
    (lam f g adj k k i).app X = (diagIso f g adj k).inv.app ((phi f g k i).obj X) :=
  eq_of_comp_eq_id _ ((adj k).counit.app ((phi f g k i).obj X)) _ (lam_counit_left f g adj k i X)
    ((diagIso f g adj k).hom_inv_id_app _)

/-- Naturality of `α_k⁻¹ : id → φ_kk`. -/
theorem diag_nat (k : I) [(g k).Full] [(g k).Faithful] {Y Z : B k} (h : Y ⟶ Z) :
    (diagIso f g adj k).inv.app Y ≫ (phi f g k k).map h = h ≫ (diagIso f g adj k).inv.app Z :=
  ((diagIso f g adj k).inv.naturality h).symm

/-- A relation `(k, i, i)`, automatic once the diagonal entry is `α_i⁻¹`. -/
theorem rel_right (k i : I) [(g i).Full] [(g i).Faithful] {Y : B k} {X : B i}
    (u : Y ⟶ (phi f g k i).obj X) :
    u ≫ (lam f g adj k i i).app X = u ≫ (phi f g k i).map ((diagIso f g adj i).inv.app X) := by
  rw [lam_app_right]

/-- A relation `(k, k, i)`, automatic once the diagonal entry is `α_k⁻¹`. -/
theorem rel_left (k i : I) [(g k).Full] [(g k).Faithful] {Y : B k} {X : B i}
    (u : Y ⟶ (phi f g k i).obj X) :
    u ≫ (lam f g adj k k i).app X = (diagIso f g adj k).inv.app Y ≫ (phi f g k k).map u := by
  rw [lam_app_left, diag_nat]

/-- The relation `(i, j, i)` with diagonal entry `α_i⁻¹` is the triangle of `λ'`. -/
theorem rel_unit (i j : I) [(g i).Full] [(g i).Faithful] (X : B i) :
    (diagIso f g adj i).inv.app X ≫ (lam f g adj i j i).app X = (lamUnit f g adj i j).app X :=
  rfl

variable [HasProductsOfShape I A]

/-- The comonad `φ = fg` over the product base. -/
noncomputable abbrev comPi : Comonad (∀ i, B i) := (adjPi f g adj).toComonad

/-- The entries `u_ki = a_k ≫ f_k(prᵢ)` of a morphism `a : X → φX`. -/
noncomputable def entree {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) (k i : I) :
    X k ⟶ (phi f g k i).obj (X i) :=
  a k ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)

/-- **The counit, entry by entry**: `a` is counital iff `α_k ∘ u_kk = id` for all `k`. -/
theorem counit_iff {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) :
    a ≫ (comPi f g adj).ε.app X = 𝟙 X ↔
      ∀ k, entree f g adj a k k ≫ (adj k).counit.app (X k) = 𝟙 _ := by
  constructor
  · intro h k
    exact (Category.assoc _ _ _).trans
      ((congrArg (a k ≫ ·) (counit_matrice f g adj X k)).symm.trans (congrFun h k))
  · intro h
    funext k
    exact (congrArg (a k ≫ ·) (counit_matrice f g adj X k)).trans
      ((Category.assoc _ _ _).symm.trans (h k))

/-- The `(j, i)` test morphisms on `φ²X`, at component `k`. -/
noncomputable abbrev test2 (X : ∀ i, B i) (k j i : I) :
    ((comPi f g adj).obj ((comPi f g adj).obj X)) k ⟶
      (phi f g k j).obj ((phi f g j i).obj (X i)) :=
  (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))

/-- Morphisms into `(φ²X)_k` are determined by the test morphisms `test2`. -/
theorem ext_phi2 [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] (X : ∀ i, B i) (k : I)
    {T : B k} (t t' : T ⟶ ((comPi f g adj).obj ((comPi f g adj).obj X)) k)
    (h : ∀ j i, t ≫ test2 f g adj X k j i = t' ≫ test2 f g adj X k j i) : t = t' := by
  have hk := (isLimitMapConeFanMkEquiv (f k) _ _)
    (isLimitOfPreserves (f k) (productIsProduct
      (fun j => (g j).obj ((f j).obj ((gPi g).obj X)))))
  refine Fan.IsLimit.hom_ext hk _ _ fun j => ?_
  have : PreservesLimitsOfShape (Discrete I) (g j) := (adj j).rightAdjoint_preservesLimits.1
  have hj := (isLimitMapConeFanMkEquiv (f j ⋙ g j ⋙ f k) _ _)
    (isLimitOfPreserves (f j ⋙ g j ⋙ f k) (productIsProduct (fun i => (g i).obj (X i))))
  refine Fan.IsLimit.hom_ext hj _ _ fun i => ?_
  have e : t ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) =
      t' ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) := by
    exact (congrArg (t ≫ ·) ((f k).map_comp _ _).symm).trans
      ((h j i).trans (congrArg (t' ≫ ·) ((f k).map_comp _ _)))
  exact (Category.assoc _ _ _).trans (e.trans (Category.assoc _ _ _).symm)

/-- `φ(a)` read on the test morphisms. -/
theorem map_test2 {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) (k j i : I) :
    (comPi f g adj).map a k ≫ test2 f g adj X k j i =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫
        (phi f g k j).map (entree f g adj a j i) := by
  change (f k).map (Limits.Pi.map fun j => (g j).map (a j)) ≫ _ = _
  simp only [test2, entree, Functor.comp_map, ← Functor.map_comp, Limits.Pi.map_π_assoc]
  exact congrArg (fun x => (f k).map (Limits.Pi.π (fun j => (g j).obj (X j)) j ≫ x))
    ((g j).map_comp _ _).symm

/-- `φ(h)` read on the projections. -/
theorem map_π {X Y : ∀ i, B i} (h : X ⟶ Y) (k i : I) :
    (comPi f g adj).map h k ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (phi f g k i).map (h i) := by
  change (f k).map (Limits.Pi.map fun j => (g j).map (h j)) ≫ _ = _
  simp only [Functor.comp_map, ← Functor.map_comp, Limits.Pi.map_π]

/-- **Coassociativity as relations between the `λ_kji`**: `a` is coassociative iff
`λ_kji ∘ u_ki = φ_kj(u_ji) ∘ u_kj` for all `k, j, i`. -/
theorem coassoc_iff [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] {X : ∀ i, B i}
    (a : X ⟶ (comPi f g adj).obj X) :
    a ≫ (comPi f g adj).δ.app X = a ≫ (comPi f g adj).map a ↔
      ∀ k j i, entree f g adj a k i ≫ (lam f g adj k j i).app (X i) =
        entree f g adj a k j ≫ (phi f g k j).map (entree f g adj a j i) := by
  have h1 : ∀ k j i, a k ≫ ((comPi f g adj).δ.app X k ≫ test2 f g adj X k j i) =
      entree f g adj a k i ≫ (lam f g adj k j i).app (X i) := fun k j i =>
    (congrArg (a k ≫ ·) (comult_matrice f g adj X k j i)).trans (Category.assoc _ _ _).symm
  have h2 : ∀ k j i, a k ≫ ((comPi f g adj).map a k ≫ test2 f g adj X k j i) =
      entree f g adj a k j ≫ (phi f g k j).map (entree f g adj a j i) := fun k j i =>
    (congrArg (a k ≫ ·) (map_test2 f g adj a k j i)).trans (Category.assoc _ _ _).symm
  constructor
  · intro h k j i
    have := congrArg (fun x => x ≫ test2 f g adj X k j i) (congrFun h k)
    exact (h1 k j i).symm.trans ((Category.assoc _ _ _).symm.trans
      (this.trans ((Category.assoc _ _ _).trans (h2 k j i))))
  · intro h
    funext k
    refine ext_phi2 f g adj X k _ _ fun j i => ?_
    exact (Category.assoc _ _ _).trans ((h1 k j i).trans ((h k j i).trans
      ((h2 k j i).symm.trans (Category.assoc _ _ _).symm)))

/-- Morphisms of coalgebras, entry by entry. -/
theorem hom_iff [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] {X Y : ∀ i, B i}
    (a : X ⟶ (comPi f g adj).obj X) (b : Y ⟶ (comPi f g adj).obj Y) (h : X ⟶ Y) :
    a ≫ (comPi f g adj).map h = h ≫ b ↔
      ∀ k i, entree f g adj a k i ≫ (phi f g k i).map (h i) = h k ≫ entree f g adj b k i := by
  have h1 : ∀ k i, a k ≫ ((comPi f g adj).map h k ≫
      (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i)) =
      entree f g adj a k i ≫ (phi f g k i).map (h i) := fun k i =>
    (congrArg (a k ≫ ·) (map_π f g adj h k i)).trans (Category.assoc _ _ _).symm
  constructor
  · intro e k i
    have := congrArg (fun x => x ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i))
      (congrFun e k)
    exact (h1 k i).symm.trans ((Category.assoc _ _ _).symm.trans
      (this.trans (Category.assoc _ _ _)))
  · intro e
    funext k
    refine Fan.IsLimit.hom_ext (matrice f g adj Y k) _ _ fun i => ?_
    exact (Category.assoc _ _ _).trans ((h1 k i).trans ((e k i).trans
      (Category.assoc _ _ _).symm))

/-- Counit of a coalgebra, with `g_k` fully faithful: the diagonal entry is `α_k⁻¹`. -/
theorem entree_diag {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X)
    (ha : a ≫ (comPi f g adj).ε.app X = 𝟙 X) (k : I) [(g k).Full] [(g k).Faithful] :
    entree f g adj a k k = (diagIso f g adj k).inv.app (X k) :=
  eq_of_comp_eq_id _ ((adj k).counit.app (X k)) _ ((counit_iff f g adj a).1 ha k)
    ((diagIso f g adj k).hom_inv_id_app _)

end MatriceRelations

section Quadruplets

variable {A : Type u₁} [Category.{v} A] {B : WalkingPair → Type u₂}
  [∀ i, Category.{v} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)
variable [(g .left).Full] [(g .left).Faithful] [(g .right).Full] [(g .right).Faithful]

/-- (pages 9–10) A quadruple `(X', X'', u', u'')`, `u' : X' → φ'(X'')`,
`u'' : X'' → φ''(X')`, subject to the two triangles `λ'(X') = φ'(u'') ∘ u'` and
`λ''(X'') = φ''(u') ∘ u''`. -/
structure Quadruplet where
  X' : B .left
  X'' : B .right
  u' : X' ⟶ (phi f g .left .right).obj X''
  u'' : X'' ⟶ (phi f g .right .left).obj X'
  tri' : (lamUnit f g adj .left .right).app X' = u' ≫ (phi f g .left .right).map u''
  tri'' : (lamUnit f g adj .right .left).app X'' = u'' ≫ (phi f g .right .left).map u'

namespace Quadruplet

variable {f g adj}

/-- A morphism of quadruples: a pair `(h', h'')` commuting with `u'` and `u''`. -/
@[ext]
structure Hom (P Q : Quadruplet f g adj) where
  h' : P.X' ⟶ Q.X'
  h'' : P.X'' ⟶ Q.X''
  w' : P.u' ≫ (phi f g .left .right).map h'' = h' ≫ Q.u' := by cat_disch
  w'' : P.u'' ≫ (phi f g .right .left).map h' = h'' ≫ Q.u'' := by cat_disch

attribute [reassoc] Hom.w' Hom.w''

instance : Category (Quadruplet f g adj) where
  Hom := Hom
  id P := { h' := 𝟙 _, h'' := 𝟙 _ }
  comp a b := { h' := a.h' ≫ b.h', h'' := a.h'' ≫ b.h''
                w' := by
                  rw [Functor.map_comp, ← Category.assoc, a.w', Category.assoc, b.w',
                    Category.assoc]
                w'' := by
                  rw [Functor.map_comp, ← Category.assoc, a.w'', Category.assoc, b.w'',
                    Category.assoc] }

@[ext]
theorem hom_ext {P Q : Quadruplet f g adj} {a b : P ⟶ Q} (h' : a.h' = b.h')
    (h'' : a.h'' = b.h'') : a = b := Hom.ext h' h''

end Quadruplet

variable [HasProductsOfShape WalkingPair A]
variable [∀ j, PreservesLimitsOfShape (Discrete WalkingPair) (f j)]

/-- A morphism given by its two components. -/
def pairHom {X Y : ∀ i, B i} (h' : X .left ⟶ Y .left) (h'' : X .right ⟶ Y .right) : X ⟶ Y
  | .left => h'
  | .right => h''

/-- (pages 9–10) A coalgebra of `φ` gives the quadruple of its off-diagonal entries. -/
noncomputable def versQuadruplets : (comPi f g adj).Coalgebra ⥤ Quadruplet f g adj where
  obj C :=
    { X' := C.A .left
      X'' := C.A .right
      u' := entree f g adj C.a .left .right
      u'' := entree f g adj C.a .right .left
      tri' := by
        have := (coassoc_iff f g adj C.a).1 C.coassoc .left .right .left
        rw [entree_diag f g adj C.a C.counit] at this
        exact this
      tri'' := by
        have := (coassoc_iff f g adj C.a).1 C.coassoc .right .left .right
        rw [entree_diag f g adj C.a C.counit] at this
        exact this }
  map {C D} h :=
    { h' := h.f .left
      h'' := h.f .right
      w' := (hom_iff f g adj C.a D.a h.f).1 h.h .left .right
      w'' := (hom_iff f g adj C.a D.a h.f).1 h.h .right .left }

/-- An object of `B' × B''` given by its two components. -/
def pairObj (X' : B .left) (X'' : B .right) : ∀ i, B i
  | .left => X'
  | .right => X''

variable {f g adj} in
/-- The matrix of a quadruple: `α⁻¹` on the diagonal, `u'` and `u''` off it. -/
noncomputable def entreesQ (Q : Quadruplet f g adj) :
    ∀ k i, pairObj Q.X' Q.X'' k ⟶ (phi f g k i).obj (pairObj Q.X' Q.X'' i)
  | .left, .left => (diagIso f g adj .left).inv.app Q.X'
  | .left, .right => Q.u'
  | .right, .left => Q.u''
  | .right, .right => (diagIso f g adj .right).inv.app Q.X''

variable {f g adj} in
/-- The coalgebra structure defined by a quadruple. -/
noncomputable def structQ (Q : Quadruplet f g adj) :
    pairObj Q.X' Q.X'' ⟶ (comPi f g adj).obj (pairObj Q.X' Q.X'') := fun k =>
  Fan.IsLimit.lift (matrice f g adj (pairObj Q.X' Q.X'') k) (entreesQ Q k)

/-- The entries of `structQ Q` are those of `entreesQ Q`. -/
theorem entree_structQ (Q : Quadruplet f g adj) (k i : WalkingPair) :
    entree f g adj (structQ Q) k i = entreesQ Q k i :=
  Fan.IsLimit.fac (matrice f g adj (pairObj Q.X' Q.X'') k) _ i

variable {f g adj} in
/-- **The quadruple defines a coalgebra**: the triangles are all the coassociativity. -/
noncomputable def coalgQ (Q : Quadruplet f g adj) : (comPi f g adj).Coalgebra where
  A := pairObj Q.X' Q.X''
  a := structQ Q
  counit := (counit_iff f g adj _).2 fun k => by
    rw [entree_structQ]
    cases k
    · exact (diagIso f g adj .left).inv_hom_id_app Q.X'
    · exact (diagIso f g adj .right).inv_hom_id_app Q.X''
  coassoc := (coassoc_iff f g adj _).2 fun k j i => by
    rw [entree_structQ, entree_structQ, entree_structQ]
    cases k <;> cases j <;> cases i
    · exact rel_right f g adj _ _ _
    · exact rel_left f g adj _ _ Q.u'
    · exact (rel_unit f g adj _ _ _).trans Q.tri'
    · exact rel_right f g adj _ _ Q.u'
    · exact rel_right f g adj _ _ Q.u''
    · exact (rel_unit f g adj _ _ _).trans Q.tri''
    · exact rel_left f g adj _ _ Q.u''
    · exact rel_right f g adj _ _ _

instance : (versQuadruplets f g adj).Faithful where
  map_injective {C D} a b e := by
    refine Comonad.Coalgebra.Hom.ext (funext fun j => ?_)
    cases j
    · exact congrArg Quadruplet.Hom.h' e
    · exact congrArg Quadruplet.Hom.h'' e

instance : (versQuadruplets f g adj).Full where
  map_surjective {C D} q := by
    refine ⟨⟨pairHom q.h' q.h'', (hom_iff f g adj C.a D.a _).2 fun k i => ?_⟩, rfl⟩
    cases k <;> cases i
    · rw [entree_diag f g adj C.a C.counit, entree_diag f g adj D.a D.counit]
      exact diag_nat f g adj _ q.h'
    · exact q.w'
    · exact q.w''
    · rw [entree_diag f g adj C.a C.counit, entree_diag f g adj D.a D.counit]
      exact diag_nat f g adj _ q.h''

instance : (versQuadruplets f g adj).EssSurj where
  mem_essImage Q := ⟨coalgQ Q, ⟨
    { hom := { h' := 𝟙 _, h'' := 𝟙 _
               w' := ((congrArg (_ ≫ ·) ((phi f g .left .right).map_id _)).trans
                 ((Category.comp_id _).trans
                   ((entree_structQ f g adj Q .left .right).trans (Category.id_comp _).symm)))
               w'' := ((congrArg (_ ≫ ·) ((phi f g .right .left).map_id _)).trans
                 ((Category.comp_id _).trans
                   ((entree_structQ f g adj Q .right .left).trans (Category.id_comp _).symm))) }
      inv := { h' := 𝟙 _, h'' := 𝟙 _
               w' := ((congrArg (_ ≫ ·) ((phi f g .left .right).map_id _)).trans
                 ((Category.comp_id _).trans ((entree_structQ f g adj Q .left .right).symm.trans
                   (Category.id_comp _).symm)))
               w'' := ((congrArg (_ ≫ ·) ((phi f g .right .left).map_id _)).trans
                 ((Category.comp_id _).trans ((entree_structQ f g adj Q .right .left).symm.trans
                   (Category.id_comp _).symm))) }
      hom_inv_id := by ext <;> exact Category.comp_id _
      inv_hom_id := by ext <;> exact Category.comp_id _ }⟩⟩

/-- **Pages 9–10: coalgebras of `φ` are the quadruples.** For two factors with `g'`, `g''`
fully faithful and `f'`, `f''` commuting with binary products, the category of coalgebras
of `φ` is equivalent to the category of quadruples `(X', X'', u', u'')`. -/
instance versQuadruplets_isEquivalence : (versQuadruplets f g adj).IsEquivalence where

/-- **Pages 9–10: the description of `A` by quadruples.** If moreover `f = (f', f'')` is
comonadic, `A` is equivalent to the category of quadruples, by
`Y ↦ (f'Y, f''Y, f'(η''_Y), f''(η'_Y))` (`quadruplet_u'`, `quadruplet_u''`). -/
theorem quadruplets [(Comonad.comparison (adjPi f g adj)).IsEquivalence] :
    (Comonad.comparison (adjPi f g adj) ⋙ versQuadruplets f g adj).IsEquivalence :=
  inferInstance

/-- The quadruple of `Y`: `u' = f'(η''_Y) : f'Y → f'g''f''Y`. -/
theorem quadruplet_u' (Y : A) :
    ((Comonad.comparison (adjPi f g adj) ⋙ versQuadruplets f g adj).obj Y).u' =
      (f .left).map ((adj .right).unit.app Y) := by
  change (f .left).map ((adjPi f g adj).unit.app Y) ≫ (f .left).map (Limits.Pi.π _ .right) = _
  rw [← Functor.map_comp, adjPi_unit_π]
  rfl

/-- The quadruple of `Y`: `u'' = f''(η'_Y) : f''Y → f''g'f'Y`. -/
theorem quadruplet_u'' (Y : A) :
    ((Comonad.comparison (adjPi f g adj) ⋙ versQuadruplets f g adj).obj Y).u'' =
      (f .right).map ((adj .left).unit.app Y) := by
  change (f .right).map ((adjPi f g adj).unit.app Y) ≫ (f .right).map (Limits.Pi.π _ .left) = _
  rw [← Functor.map_comp, adjPi_unit_π]
  rfl

end Quadruplets
end Grothendieck.Folder19

/-!
## The degenerate case (pages 10–11)

> Si `φ'φ''` et `φ''φ'` sont constants de valeur l'objet final, les deux triangles sont
> vides de contenu et `A` est simplement la catégorie des quadruplets, sans condition.
> […] image essentielle de `g'` : `u''` est un isomorphisme ; image essentielle de
> `g''` : `u'` est un isomorphisme.

* `essImage_iff` — for any index set `I`: if `g_i` is fully faithful and `f = (f_j)` is
  conservative, `Y ∈ essImage g_i` iff `f_j(η_i,Y)` is invertible for every `j ≠ i`
  (for `j = i` it always is). No degeneracy is needed.
* `Quadruplet.degenere` — in the degenerate case every `(X', X'', u', u'')` is a
  quadruple: the triangles land in a final object.
* `essImage_g'_iff`, `essImage_g''_iff` — with `f` comonadic, the quadruple of an object
  `Y` (`quadruplets`) lies in the essential image of `g'` iff `u''` is invertible, and in
  that of `g''` iff `u'` is: `essImage_g'_quadruplets`, `essImage_g''_quadruplets` state it
  for an arbitrary quadruple, through `Φ = comparison ⋙ versQuadruplets`. The degenerate
  hypothesis is not used: the criterion of the page holds whenever `g'`, `g''` are fully
  faithful and `f` is comonadic.
* `essImage_inter` — the intersection is « `u'` and `u''` invertible »;
  `final_of_inter` — in the degenerate case, `X'` and `X''` are then final.
-/

namespace Grothendieck.Folder19

open CategoryTheory Limits

universe w' v' u₁' u₂'

section CasDegenere

variable {I : Type w'} {A : Type u₁'} [Category.{v'} A] {B : I → Type u₂'}
  [∀ i, Category.{v'} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- **The essential image of `g_i`.** If `g_i` is fully faithful and `f = (f_j)` is
conservative, `Y` lies in the essential image of `g_i` iff `f_j(η_i,Y)` is invertible for
every `j ≠ i`. -/
theorem essImage_iff [DecidableEq I] (i : I) [(g i).Full] [(g i).Faithful]
    [(Functor.pi' f).ReflectsIsomorphisms] (Y : A) :
    (g i).essImage Y ↔ ∀ j, j ≠ i → IsIso ((f j).map ((adj i).unit.app Y)) := by
  rw [← (adj i).isIso_unit_app_iff_mem_essImage]
  refine ⟨fun _ j _ => inferInstance, fun h => ?_⟩
  refine (isIso_iff_of_reflects_iso _ (Functor.pi' f)).1 ((isIso_pi_iff _).2 fun j => ?_)
  change IsIso ((f j).map ((adj i).unit.app Y))
  by_cases hj : j = i
  · subst hj
    infer_instance
  · exact h j hj

/-- A comonadic `f` is conservative. -/
theorem reflectsIso_of_comonadic [HasProductsOfShape I A]
    [(Comonad.comparison (adjPi f g adj)).IsEquivalence] :
    (Functor.pi' f).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_iso (Comonad.comparisonForget (adjPi f g adj))

end CasDegenere

section CasDegenereDeux

variable {A : Type u₁'} [Category.{v'} A] {B : WalkingPair → Type u₂'}
  [∀ i, Category.{v'} (B i)]
variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)
variable [(g .left).Full] [(g .left).Faithful] [(g .right).Full] [(g .right).Faithful]

variable {f g adj} in
/-- **The degenerate case: no condition.** If `φ'φ''` and `φ''φ'` take final values, every
`(X', X'', u', u'')` is a quadruple. -/
def Quadruplet.degenere
    (h' : ∀ X, IsTerminal ((phi f g .left .right).obj ((phi f g .right .left).obj X)))
    (h'' : ∀ X, IsTerminal ((phi f g .right .left).obj ((phi f g .left .right).obj X)))
    (X' : B .left) (X'' : B .right) (u' : X' ⟶ (phi f g .left .right).obj X'')
    (u'' : X'' ⟶ (phi f g .right .left).obj X') : Quadruplet f g adj where
  X' := X'
  X'' := X''
  u' := u'
  u'' := u''
  tri' := (h' X').hom_ext _ _
  tri'' := (h'' X'').hom_ext _ _

variable {f g adj} in
/-- An isomorphism of quadruples carries the invertibility of `u''`. -/
theorem Quadruplet.isIso_u''_of_iso {P Q : Quadruplet f g adj} (e : P ≅ Q) [IsIso P.u''] :
    IsIso Q.u'' := by
  have hX' : IsIso e.hom.h' := ⟨e.inv.h', congrArg Quadruplet.Hom.h' e.hom_inv_id,
    congrArg Quadruplet.Hom.h' e.inv_hom_id⟩
  have hX'' : IsIso e.inv.h'' := ⟨e.hom.h'', congrArg Quadruplet.Hom.h'' e.inv_hom_id,
    congrArg Quadruplet.Hom.h'' e.hom_inv_id⟩
  have : Q.u'' = e.inv.h'' ≫ P.u'' ≫ (phi f g .right .left).map e.hom.h' := by
    rw [e.hom.w'', ← Category.assoc,
      show e.inv.h'' ≫ e.hom.h'' = 𝟙 _ from congrArg Quadruplet.Hom.h'' e.inv_hom_id,
      Category.id_comp]
  rw [this]
  infer_instance

variable {f g adj} in
/-- An isomorphism of quadruples carries the invertibility of `u'`. -/
theorem Quadruplet.isIso_u'_of_iso {P Q : Quadruplet f g adj} (e : P ≅ Q) [IsIso P.u'] :
    IsIso Q.u' := by
  have hX'' : IsIso e.hom.h'' := ⟨e.inv.h'', congrArg Quadruplet.Hom.h'' e.hom_inv_id,
    congrArg Quadruplet.Hom.h'' e.inv_hom_id⟩
  have hX' : IsIso e.inv.h' := ⟨e.hom.h', congrArg Quadruplet.Hom.h' e.inv_hom_id,
    congrArg Quadruplet.Hom.h' e.hom_inv_id⟩
  have : Q.u' = e.inv.h' ≫ P.u' ≫ (phi f g .left .right).map e.hom.h'' := by
    rw [e.hom.w', ← Category.assoc,
      show e.inv.h' ≫ e.hom.h' = 𝟙 _ from congrArg Quadruplet.Hom.h' e.inv_hom_id,
      Category.id_comp]
  rw [this]
  infer_instance

/-- For a fully faithful `Φ`, `Φ(Y)` is in the essential image of `G ⋙ Φ` iff `Y` is in
that of `G`. -/
theorem essImage_comp_obj_iff {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (Φ : D ⥤ E) [Φ.Full] [Φ.Faithful] (Y : D) :
    (G ⋙ Φ).essImage (Φ.obj Y) ↔ G.essImage Y :=
  ⟨fun ⟨X, ⟨e⟩⟩ => ⟨X, ⟨Φ.preimageIso e⟩⟩, fun ⟨X, ⟨e⟩⟩ => ⟨X, ⟨Φ.mapIso e⟩⟩⟩

variable [HasProductsOfShape WalkingPair A]
variable [∀ j, PreservesLimitsOfShape (Discrete WalkingPair) (f j)]
variable [(Comonad.comparison (adjPi f g adj)).IsEquivalence]

/-- `Φ : A ≃ quadruples`, `Y ↦ (f'Y, f''Y, f'(η''_Y), f''(η'_Y))`. -/
noncomputable abbrev versQ : A ⥤ Quadruplet f g adj :=
  Comonad.comparison (adjPi f g adj) ⋙ versQuadruplets f g adj

/-- **Pages 10–11: the essential image of `g'`.** `Y` lies in the essential image of `g'`
iff the `u''` of its quadruple, `f''(η'_Y)`, is invertible. -/
theorem essImage_g'_iff (Y : A) :
    (g .left).essImage Y ↔ IsIso ((versQ f g adj).obj Y).u'' := by
  have := reflectsIso_of_comonadic f g adj
  rw [essImage_iff f g adj .left Y, quadruplet_u'']
  exact ⟨fun h => h .right (by decide), fun h j hj => by cases j <;> first | exact h | exact absurd rfl hj⟩

/-- **Pages 10–11: the essential image of `g''`.** `Y` lies in the essential image of `g''`
iff the `u'` of its quadruple, `f'(η''_Y)`, is invertible. -/
theorem essImage_g''_iff (Y : A) :
    (g .right).essImage Y ↔ IsIso ((versQ f g adj).obj Y).u' := by
  have := reflectsIso_of_comonadic f g adj
  rw [essImage_iff f g adj .right Y, quadruplet_u']
  exact ⟨fun h => h .left (by decide), fun h j hj => by cases j <;> first | exact h | exact absurd rfl hj⟩

/-- **Pages 10–11, on the quadruples.** A quadruple lies in the essential image of
`g' ⋙ Φ` iff `u''` is invertible. -/
theorem essImage_g'_quadruplets (Q : Quadruplet f g adj) :
    (g .left ⋙ versQ f g adj).essImage Q ↔ IsIso Q.u'' := by
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := versQ f g adj) Q
  have h1 : (g .left ⋙ versQ f g adj).essImage Q ↔
      (g .left ⋙ versQ f g adj).essImage ((versQ f g adj).obj Y) :=
    ⟨.ofIso e.symm, .ofIso e⟩
  rw [h1, essImage_comp_obj_iff, essImage_g'_iff f g adj]
  exact ⟨fun _ => Quadruplet.isIso_u''_of_iso e, fun _ => Quadruplet.isIso_u''_of_iso e.symm⟩

/-- **Pages 10–11, on the quadruples.** A quadruple lies in the essential image of
`g'' ⋙ Φ` iff `u'` is invertible. -/
theorem essImage_g''_quadruplets (Q : Quadruplet f g adj) :
    (g .right ⋙ versQ f g adj).essImage Q ↔ IsIso Q.u' := by
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := versQ f g adj) Q
  have h1 : (g .right ⋙ versQ f g adj).essImage Q ↔
      (g .right ⋙ versQ f g adj).essImage ((versQ f g adj).obj Y) :=
    ⟨.ofIso e.symm, .ofIso e⟩
  rw [h1, essImage_comp_obj_iff, essImage_g''_iff f g adj]
  exact ⟨fun _ => Quadruplet.isIso_u'_of_iso e, fun _ => Quadruplet.isIso_u'_of_iso e.symm⟩

/-- The intersection of the two essential images: `u'` and `u''` invertible. -/
theorem essImage_inter (Q : Quadruplet f g adj) :
    ((g .left ⋙ versQ f g adj).essImage Q ∧ (g .right ⋙ versQ f g adj).essImage Q) ↔
      (IsIso Q.u' ∧ IsIso Q.u'') := by
  rw [essImage_g'_quadruplets, essImage_g''_quadruplets]
  exact And.comm

/-- In the degenerate case, a quadruple of the intersection has `X'` and `X''` final. -/
theorem final_of_inter
    (h' : ∀ X, IsTerminal ((phi f g .left .right).obj ((phi f g .right .left).obj X)))
    (h'' : ∀ X, IsTerminal ((phi f g .right .left).obj ((phi f g .left .right).obj X)))
    (Q : Quadruplet f g adj) (hQ : (g .left ⋙ versQ f g adj).essImage Q ∧
      (g .right ⋙ versQ f g adj).essImage Q) :
    Nonempty (IsTerminal Q.X') ∧ Nonempty (IsTerminal Q.X'') := by
  obtain ⟨_, _⟩ := (essImage_inter f g adj Q).1 hQ
  exact ⟨⟨(h' Q.X').ofIso (asIso (Q.u' ≫ (phi f g .left .right).map Q.u'')).symm⟩,
    ⟨(h'' Q.X'').ofIso (asIso (Q.u'' ≫ (phi f g .right .left).map Q.u')).symm⟩⟩

end CasDegenereDeux

end Grothendieck.Folder19
