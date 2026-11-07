module

public import Mathlib
public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Tactic.TFAE
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Grothendieck.Upstream.AdjunctionIdempotent
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

@[expose] public section


/-!
# Folder 161-1: the fixed part of an adjunction, idempotent adjunctions, local objects

The modernised reading `transcripts/161-1/161-1.modern.tex` (manuscript pages 3–7)
states, for an adjunction `u ⊣ v` between `E` and `F`, unit `η`, counit `ε`:

> **(1)** Pour une sous-catégorie pleine `E' ⊂ E`,
> `u|E'` pl. fidèle et `vu(E') ⊂ Ē'` ⟺ `∀ Y ∈ E', η_Y : Y ⥲ vu(Y)`.
>
> Le manuscrit se demande en marge si la seconde condition de (1) est vraiment
> nécessaire — « donner un exemple montrant que cette condition n'est pas
> surabondante, avec `E'` réduit à un élément ». Elle l'est : la pleine fidélité
> de `u|E'` ne force pas `vu` à ramener `E'` dans `Ē'`.

> **Adjonctions idempotentes** (page 5) : `ηv : v ⥲ vuv`, et de même
> `εu : uvu ⥲ u` … Fait aujourd'hui classique : chacune des quatre conditions
> (`ηv`, `vε`, `εu`, `uη` inversible) implique les trois autres, de sorte que
> les paires du manuscrit sont redondantes.

> **Objets locaux** (pages 6–7) : `α : E₁ → E` pleinement fidèle d'adjoint à
> gauche `α'`, `Σ` la classe des flèches que `α'` inverse. La page vérifie que
> `(f : X → Y) ∈ Σ ⟺ Hom_E(Y, αZ₁) ≃ Hom_E(X, αZ₁)` pour tout `Z₁ ∈ E₁`, et
> conclut « Or c'est vrai sauf erreur… » : un objet `Σ`-local est dans l'image
> essentielle de `α`.

What is proved here, all as the reading states it:

* `condition1` — the equivalence (1), for any full subcategory given by an
  `ObjectProperty`, with `Ē'` its closure under isomorphism.
* `condition1_non_surabondante` — the example the margin asks for, with `E'`
  reduced to one object: `E = Type`, `F` the one-point category, `u` the unique
  functor, `v` picking the one-point set, `E' = {∅}`. Then `u|E'` is fully
  faithful but `vu(∅) = *` is not isomorphic to `∅`. So the reading's answer
  « Elle l'est » is right, and this is a witness.
* `idempotent_tfae` — the four conditions `ηv`, `vε`, `εu`, `uη` invertible are
  equivalent, which is the footnote's claim; hence the manuscript's paired
  condition 2 is equivalent to either half (`condition2_iff`).
* `sigma_iff` — the page-7 check that `f ∈ Σ` iff `f` is bijective on maps into
  every `αZ₁`. This one is in mathlib, as `ObjectProperty.isLocal_iff_isIso_map`.
* `local_mem_essImage` and `local_iff_mem_essImage` — « Or c'est vrai » : the
  `Σ`-local objects are exactly the essential image of `α`.
* `condition2` — the dual equivalence (2), for `F' ⊂ F`.
* `five_conditions_tfae` — page 3, c): for strictly full `E'`, `F'`, the
  conditions 1.–4. are equivalent (the page's 5. repeats 2.); `beta_alpha`,
  `alpha_beta` — the bijection `E' ↦ \overline{u(E')}`, `F' ↦ \overline{v(F')}`.
* `E0_iff`, `F0_iff`, `fixedEquiv` — page 4: `E₀ = \overline{v(F₀)}`,
  `F₀ = \overline{u(E₀)}`, and `u`, `v` induce quasi-inverse equivalences `E₀ ≃ F₀`.
* `condition1_p5_iff`, `reflectorAdj`, `coreflectorAdj`, `condition4`,
  `condition4'`, `reflector0_isLocalization` — page 5: conditions 1), 3), 4):
  `E₀` reflective with reflector `v₀ ∘ u'`, `F₀` coreflective with coreflector
  `u₀ ∘ v'`, and `u ≅ β u₀ α'`, `v ≅ α v₀ β'` with `α'` a localization.
* `reflector0_preservesColimits`, `E0_ι_preservesLimits`, `E0_hasColimits` and
  their duals — the reflector preserves colimits, `E₀` is closed under limits
  and has the colimits of `E`; dually for `F₀`.
* `descent`, `descent_isLeftAdjoint` — page 6: a presheaf `ψ` on `E₁` with
  `ψ ∘ α'` representable is representable; hence if `β ∘ α'` has a right
  adjoint, so has `β` — without the full faithfulness of `β` the page assumes.

**What the formalisation finds.** Nothing false. The equivalence (1) needs
nothing beyond the adjunction; the idempotence conditions are redundant exactly
as the footnote says; the local-object statement holds for an arbitrary
reflective subcategory. The fifth condition of page 3 is the second one again.
Page 6's descent of adjoints holds, and does not need `β` fully faithful. The
rest of the folder (the free symmetric monoidal category, the sign `ε(L)` of
Picard categories, the Kan-extension and Giraud material of pages 15–19) is not
formalised here.

What this certifies is that the reading holds together, not that it is what the
pages say (issue #26).
-/

namespace Grothendieck.Folder161_1

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {u : E ⥤ F} {v : F ⥤ E} (adj : u ⊣ v)

/-- Composing `u.map` with the adjunction bijection gives `f ↦ f ≫ η_Y`: this is
the page's « n'est autre que `Hom(X, η_Y)` ». -/
theorem map_bijective_iff (X Y : E) :
    Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y)) ↔
      Function.Bijective (fun f : X ⟶ Y => f ≫ adj.unit.app Y) := by
  have : (fun f : X ⟶ Y => f ≫ adj.unit.app Y) = (adj.homEquiv X (u.obj Y)) ∘ u.map := by
    funext f
    simp [Adjunction.homEquiv_unit]
  rw [this, Equiv.comp_bijective]

/-- **(1).** For a full subcategory `E'` of `E` (given by the property `P`):
`u` is fully faithful on `E'` and `vu` sends `E'` into its isomorphism closure
if and only if `η_Y` is an isomorphism for every `Y ∈ E'`. -/
theorem condition1 (P : ObjectProperty E) :
    ((∀ X Y, P X → P Y → Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y))) ∧
        ∀ Y, P Y → P.isoClosure (v.obj (u.obj Y))) ↔
      ∀ Y, P Y → IsIso (adj.unit.app Y) := by
  constructor
  · rintro ⟨hff, hvu⟩ Y hY
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hvu Y hY
    have bZ := (map_bijective_iff adj Z Y).1 (hff Z Y hZ hY)
    have bY := (map_bijective_iff adj Y Y).1 (hff Y Y hY hY)
    -- A section `g` of `η_Y`, through `Z ≅ vu(Y)`.
    obtain ⟨g, hg⟩ := bZ.2 e.inv
    have hg' : g ≫ adj.unit.app Y = e.inv := hg
    refine ⟨e.hom ≫ g, ?_, ?_⟩
    · apply bY.1
      show (adj.unit.app Y ≫ e.hom ≫ g) ≫ adj.unit.app Y = 𝟙 Y ≫ adj.unit.app Y
      rw [Category.assoc, Category.assoc, hg', e.hom_inv_id]
      simp
    · rw [Category.assoc, hg', e.hom_inv_id]
      rfl
  · intro h
    exact ⟨fun X Y _ hY => (map_bijective_iff adj X Y).2
      (have := h Y hY; (asIso (adj.unit.app Y)).homToEquiv.bijective),
      fun Y hY => ⟨Y, hY, ⟨(have := h Y hY; asIso (adj.unit.app Y)).symm⟩⟩⟩

section Example

/-- The unique functor from `Type` to the one-point category. -/
def toPoint : Type ⥤ Discrete PUnit.{1} := (Functor.const Type).obj ⟨PUnit.unit⟩

/-- The functor picking the one-point set. -/
def fromPoint : Discrete PUnit.{1} ⥤ Type := (Functor.const (Discrete PUnit.{1})).obj PUnit

/-- `toPoint ⊣ fromPoint`: the one-point set is terminal. -/
def adjPoint : toPoint ⊣ fromPoint where
  unit := { app := fun _ => TypeCat.ofHom fun _ => PUnit.unit }
  counit := { app := fun _ => 𝟙 _ }

/-- **The margin's example**, with `E'` reduced to one object, `∅`. `u` is fully
faithful on `{∅}`, but `vu(∅)` is not isomorphic to `∅`, and `η_∅` is not an
isomorphism: the second condition of (1) is not superfluous. -/
theorem condition1_non_surabondante :
    Function.Bijective (toPoint.map : (Empty ⟶ Empty) → (toPoint.obj Empty ⟶ toPoint.obj Empty)) ∧
      ¬ (ObjectProperty.isoClosure (· = Empty)) (fromPoint.obj (toPoint.obj Empty)) ∧
      ¬ IsIso (adjPoint.unit.app Empty) := by
  exact ⟨⟨fun f g _ => by ext (x : Empty); exact x.elim, fun _ => ⟨𝟙 _, Subsingleton.elim _ _⟩⟩,
    fun ⟨_, rfl, ⟨e⟩⟩ => (e.hom PUnit.unit).elim,
    fun _ => (inv (adjPoint.unit.app Empty) PUnit.unit).elim⟩

end Example

section Idempotent

/-- An endomorphism equal to the identity is an isomorphism. -/
theorem isIso_of_eq_id {C : Type*} [Category C] {X : C} {f : X ⟶ X} (h : f = 𝟙 X) :
    IsIso f :=
  h ▸ inferInstance

/-- Under idempotency, `vu(η_X) = η_{vuX}`. -/
theorem vu_unit_eq (h : ∀ P, IsIso (adj.unit.app (v.obj P))) (X : E) :
    v.map (u.map (adj.unit.app X)) = adj.unit.app (v.obj (u.obj X)) := by
  have := isIso_of_eq_id (adj.right_triangle_components (u.obj X))
  have := h (u.obj X)
  have : IsIso (v.map (adj.counit.app (u.obj X))) := IsIso.of_isIso_comp_left (adj.unit.app _) _
  rw [← cancel_mono (v.map (adj.counit.app (u.obj X))), ← Functor.map_comp]
  simp

/-- Under idempotency, `uv(ε_P) = ε_{uvP}`. -/
theorem uv_counit_eq (h : ∀ X, IsIso (adj.counit.app (u.obj X))) (P : F) :
    u.map (v.map (adj.counit.app P)) = adj.counit.app (u.obj (v.obj P)) := by
  have := isIso_of_eq_id (adj.left_triangle_components (v.obj P))
  have := h (v.obj P)
  have : IsIso (u.map (adj.unit.app (v.obj P))) := IsIso.of_isIso_comp_right _ (adj.counit.app _)
  rw [← cancel_epi (u.map (adj.unit.app (v.obj P))), ← Functor.map_comp]
  simp

/-- **Idempotent adjunctions.** The four conditions `ηv`, `vε`, `εu`, `uη`
invertible are equivalent. -/
theorem idempotent_tfae :
    List.TFAE [∀ P, IsIso (adj.unit.app (v.obj P)), ∀ P, IsIso (v.map (adj.counit.app P)),
      ∀ X, IsIso (adj.counit.app (u.obj X)), ∀ X, IsIso (u.map (adj.unit.app X))] :=
  Adjunction.idempotent_tfae adj

/-- The manuscript's condition 2, `ηv` and `εu` both invertible, is equivalent to
its first half alone: the pair is redundant. -/
theorem condition2_iff :
    ((∀ P, IsIso (adj.unit.app (v.obj P))) ∧ ∀ X, IsIso (adj.counit.app (u.obj X))) ↔
      ∀ P, IsIso (adj.unit.app (v.obj P)) :=
  ⟨And.left, fun h => ⟨h, ((idempotent_tfae adj).out 1 3).1 h⟩⟩

end Idempotent

section Dual

/-- Dual of `map_bijective_iff`: composing `v.map` with the inverse adjunction
bijection gives `g ↦ ε_P ≫ g`, the page's « se déduit des `j(P)` par
`Hom(j(P), Q)` ». -/
theorem map_bijective_iff_counit (P Q : F) :
    Function.Bijective (v.map : (P ⟶ Q) → (v.obj P ⟶ v.obj Q)) ↔
      Function.Bijective (fun g : P ⟶ Q => adj.counit.app P ≫ g) := by
  have : (fun g : P ⟶ Q => adj.counit.app P ≫ g) = (adj.homEquiv (v.obj P) Q).symm ∘ v.map := by
    funext g
    simp [Adjunction.homEquiv_counit]
  rw [this, Equiv.comp_bijective]

/-- **(2).** For a full subcategory `F'` of `F` (given by the property `P`):
`v` is fully faithful on `F'` and `uv` sends `F'` into its isomorphism closure
if and only if `ε_P` is an isomorphism for every `P ∈ F'`. -/
theorem condition2 (P : ObjectProperty F) :
    ((∀ X Y, P X → P Y → Function.Bijective (v.map : (X ⟶ Y) → (v.obj X ⟶ v.obj Y))) ∧
        ∀ Y, P Y → P.isoClosure (u.obj (v.obj Y))) ↔
      ∀ Y, P Y → IsIso (adj.counit.app Y) := by
  constructor
  · rintro ⟨hff, huv⟩ Y hY
    obtain ⟨Z, hZ, ⟨e⟩⟩ := huv Y hY
    have bZ := (map_bijective_iff_counit adj Y Z).1 (hff Y Z hY hZ)
    have bY := (map_bijective_iff_counit adj Y Y).1 (hff Y Y hY hY)
    -- A retraction `g` of `ε_Y`, through `uv(Y) ≅ Z`.
    obtain ⟨g, hg⟩ := bZ.2 e.hom
    have hg' : adj.counit.app Y ≫ g = e.hom := hg
    refine ⟨g ≫ e.inv, by simp [reassoc_of% hg'], ?_⟩
    apply bY.1
    simp [reassoc_of% hg']
  · intro h
    refine ⟨fun X Y hX _ => ?_, fun Y hY => ⟨Y, hY, ⟨(have := h Y hY; asIso (adj.counit.app Y))⟩⟩⟩
    rw [map_bijective_iff_counit adj]
    have := h X hX
    exact ⟨fun a b hab => (cancel_epi (adj.counit.app X)).1 hab,
      fun g => ⟨inv (adj.counit.app X) ≫ g, by simp⟩⟩

end Dual

section Fixed

/-! ### The fixed parts `E₀` and `F₀` (page 4) -/

/-- `E₀`: the objects of `E` where the unit is invertible. -/
def E0 : ObjectProperty E := fun Y => IsIso (adj.unit.app Y)

/-- `F₀`: the objects of `F` where the counit is invertible. -/
def F0 : ObjectProperty F := fun P => IsIso (adj.counit.app P)

/-- `E₀` is the largest full subcategory satisfying (1). -/
theorem condition1_iff_le_E0 (P : ObjectProperty E) :
    ((∀ X Y, P X → P Y → Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y))) ∧
        ∀ Y, P Y → P.isoClosure (v.obj (u.obj Y))) ↔ P ≤ E0 adj :=
  condition1 adj P

/-- `F₀` is the largest full subcategory satisfying (2). -/
theorem condition2_iff_le_F0 (P : ObjectProperty F) :
    ((∀ X Y, P X → P Y → Function.Bijective (v.map : (X ⟶ Y) → (v.obj X ⟶ v.obj Y))) ∧
        ∀ Y, P Y → P.isoClosure (u.obj (v.obj Y))) ↔ P ≤ F0 adj :=
  condition2 adj P

theorem u_mem_F0 {Y : E} (h : E0 adj Y) : F0 adj (u.obj Y) := by
  have : IsIso (adj.unit.app Y) := h
  have := isIso_of_eq_id (adj.left_triangle_components Y)
  exact IsIso.of_isIso_comp_left (u.map (adj.unit.app Y)) (adj.counit.app (u.obj Y))

theorem v_mem_E0 {P : F} (h : F0 adj P) : E0 adj (v.obj P) := by
  have : IsIso (adj.counit.app P) := h
  have := isIso_of_eq_id (adj.right_triangle_components P)
  exact IsIso.of_isIso_comp_right (adj.unit.app (v.obj P)) (v.map (adj.counit.app P))

instance : (E0 adj).IsClosedUnderIsomorphisms where
  of_iso {Y Y'} e h := by
    have : IsIso (adj.unit.app Y) := h
    have hη : adj.unit.app Y' = e.inv ≫ adj.unit.app Y ≫ v.map (u.map e.hom) := by simp
    show IsIso (adj.unit.app Y')
    rw [hη]
    infer_instance

instance : (F0 adj).IsClosedUnderIsomorphisms where
  of_iso {P P'} e h := by
    have : IsIso (adj.counit.app P) := h
    have hε : adj.counit.app P' = u.map (v.map e.inv) ≫ adj.counit.app P ≫ e.hom := by simp
    show IsIso (adj.counit.app P')
    rw [hε]
    infer_instance

/-- **Page 4.** `F₀ = \overline{u(E₀)}`. -/
theorem F0_iff (P : F) : F0 adj P ↔ ∃ Y, E0 adj Y ∧ Nonempty (u.obj Y ≅ P) := by
  refine ⟨fun h => ⟨v.obj P, v_mem_E0 adj h, ⟨(have : IsIso (adj.counit.app P) := h;
    asIso (adj.counit.app P))⟩⟩, ?_⟩
  rintro ⟨Y, hY, ⟨e⟩⟩
  exact (F0 adj).prop_of_iso e (u_mem_F0 adj hY)

/-- **Page 4.** `E₀ = \overline{v(F₀)}`. -/
theorem E0_iff (Y : E) : E0 adj Y ↔ ∃ P, F0 adj P ∧ Nonempty (v.obj P ≅ Y) := by
  refine ⟨fun h => ⟨u.obj Y, u_mem_F0 adj h, ⟨(have : IsIso (adj.unit.app Y) := h;
    (asIso (adj.unit.app Y)).symm)⟩⟩, ?_⟩
  rintro ⟨P, hP, ⟨e⟩⟩
  exact (E0 adj).prop_of_iso e (v_mem_E0 adj hP)

/-- `η_Y` as an isomorphism, for `Y ∈ E₀`. -/
noncomputable def unitIso0 (Y : (E0 adj).FullSubcategory) : Y.obj ≅ v.obj (u.obj Y.obj) :=
  @asIso _ _ _ _ (adj.unit.app Y.obj) Y.2

@[simp] theorem unitIso0_hom (Y : (E0 adj).FullSubcategory) :
    (unitIso0 adj Y).hom = adj.unit.app Y.obj := rfl

/-- `ε_P` as an isomorphism, for `P ∈ F₀`. -/
noncomputable def counitIso0 (P : (F0 adj).FullSubcategory) : u.obj (v.obj P.obj) ≅ P.obj :=
  @asIso _ _ _ _ (adj.counit.app P.obj) P.2

@[simp] theorem counitIso0_hom (P : (F0 adj).FullSubcategory) :
    (counitIso0 adj P).hom = adj.counit.app P.obj := rfl

/-- `u` restricted and corestricted to `E₀ → F₀`. -/
def u0 : (E0 adj).FullSubcategory ⥤ (F0 adj).FullSubcategory :=
  (F0 adj).lift ((E0 adj).ι ⋙ u) fun Y => u_mem_F0 adj Y.2

/-- `v` restricted and corestricted to `F₀ → E₀`. -/
def v0 : (F0 adj).FullSubcategory ⥤ (E0 adj).FullSubcategory :=
  (E0 adj).lift ((F0 adj).ι ⋙ v) fun P => v_mem_E0 adj P.2

/-- **Page 4.** `u` and `v` induce quasi-inverse equivalences `E₀ ≃ F₀`, with
the unit and counit of the adjunction as the two isomorphisms. -/
noncomputable def fixedEquiv : (E0 adj).FullSubcategory ≌ (F0 adj).FullSubcategory :=
  CategoryTheory.Equivalence.mk (u0 adj) (v0 adj)
    (NatIso.ofComponents (fun Y => (E0 adj).isoMk (unitIso0 adj Y))
      (fun f => ObjectProperty.hom_ext _ (by simp [u0, v0])))
    (NatIso.ofComponents (fun P => (F0 adj).isoMk (counitIso0 adj P))
      (fun f => ObjectProperty.hom_ext _ (by simp [u0, v0])))

theorem fixedEquiv_functor : (fixedEquiv adj).functor = u0 adj := rfl

theorem fixedEquiv_inverse : (fixedEquiv adj).inverse = v0 adj := rfl

end Fixed

section FiveConditions

/-! ### Page 3, c): the correspondence and the five conditions

`E' ⊂ E` and `F' ⊂ F` strictly full (closed under isomorphism). The restrictions
`u' : E' → F'`, `v' : F' → E'` are stated through `u` and `v` themselves: `u'`
fully faithful is bijectivity of `u.map` on `E'`, and `u'` an equivalence is
`u'` fully faithful and essentially surjective onto `F'`. -/

variable (E' : ObjectProperty E) (F' : ObjectProperty F)

/-- `u(E') ⊂ F'` and `v(F') ⊂ E'`. -/
def Stable : Prop := (∀ Y, E' Y → F' (u.obj Y)) ∧ ∀ P, F' P → E' (v.obj P)

/-- `u'` fully faithful. -/
def UFF : Prop := ∀ X Y, E' X → E' Y → Function.Bijective (u.map : (X ⟶ Y) → (u.obj X ⟶ u.obj Y))

/-- `v'` fully faithful. -/
def VFF : Prop := ∀ X Y, F' X → F' Y → Function.Bijective (v.map : (X ⟶ Y) → (v.obj X ⟶ v.obj Y))

/-- `u'` essentially surjective onto `F'`. -/
def UES : Prop := ∀ P, F' P → ∃ Y, E' Y ∧ Nonempty (u.obj Y ≅ P)

/-- `v'` essentially surjective onto `E'`. -/
def VES : Prop := ∀ Y, E' Y → ∃ P, F' P ∧ Nonempty (v.obj P ≅ Y)

/-- Condition 1. of page 3: `E'` satisfies (1), `F'` satisfies (2), and
`F' = \overline{u(E')}`, `E' = \overline{v(F')}`. -/
def Corresp : Prop :=
  (∀ Y, E' Y → IsIso (adj.unit.app Y)) ∧ (∀ P, F' P → IsIso (adj.counit.app P)) ∧
    (∀ P, F' P ↔ ∃ Y, E' Y ∧ Nonempty (u.obj Y ≅ P)) ∧
    ∀ Y, E' Y ↔ ∃ P, F' P ∧ Nonempty (v.obj P ≅ Y)

theorem stable_of_corresp (h : Corresp adj E' F') : Stable (u := u) (v := v) E' F' :=
  ⟨fun Y hY => (h.2.2.1 _).2 ⟨Y, hY, ⟨Iso.refl _⟩⟩, fun P hP => (h.2.2.2 _).2 ⟨P, hP, ⟨Iso.refl _⟩⟩⟩

theorem unit_of_stable (hs : Stable (u := u) (v := v) E' F') (hu : UFF (u := u) E') :
    ∀ Y, E' Y → IsIso (adj.unit.app Y) :=
  (condition1 adj E').1 ⟨hu, fun Y hY => ⟨_, hs.2 _ (hs.1 Y hY), ⟨Iso.refl _⟩⟩⟩

theorem counit_of_stable (hs : Stable (u := u) (v := v) E' F') (hv : VFF (v := v) F') :
    ∀ P, F' P → IsIso (adj.counit.app P) :=
  (condition2 adj F').1 ⟨hv, fun P hP => ⟨_, hs.1 _ (hs.2 P hP), ⟨Iso.refl _⟩⟩⟩

variable [E'.IsClosedUnderIsomorphisms] [F'.IsClosedUnderIsomorphisms]

theorem corresp_of (hs : Stable (u := u) (v := v) E' F') (hη : ∀ Y, E' Y → IsIso (adj.unit.app Y))
    (hε : ∀ P, F' P → IsIso (adj.counit.app P)) : Corresp adj E' F' := by
  refine ⟨hη, hε, fun P => ⟨fun hP => ?_, ?_⟩, fun Y => ⟨fun hY => ?_, ?_⟩⟩
  · have := hε P hP
    exact ⟨v.obj P, hs.2 P hP, ⟨asIso (adj.counit.app P)⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact F'.prop_of_iso e (hs.1 Y hY)
  · have := hη Y hY
    exact ⟨u.obj Y, hs.1 Y hY, ⟨(asIso (adj.unit.app Y)).symm⟩⟩
  · rintro ⟨P, hP, ⟨e⟩⟩
    exact E'.prop_of_iso e (hs.2 P hP)

/-- **Page 3, c).** For strictly full `E'`, `F'`, the conditions
1. `E'` satisfies (1), `F'` satisfies (2), and they correspond;
2. `u(E') ⊂ F'`, `v(F') ⊂ E'`, and `u'`, `v'` fully faithful;
3. — and `u'` is an equivalence;
4. — and `v'` is an equivalence;
are equivalent. The page's fifth condition, « —— et `u'` et `v'` pl. fid. »,
repeats the second word for word. -/
theorem five_conditions_tfae :
    List.TFAE [Corresp adj E' F',
      Stable (u := u) (v := v) E' F' ∧ UFF (u := u) E' ∧ VFF (v := v) F',
      Stable (u := u) (v := v) E' F' ∧ UFF (u := u) E' ∧ UES (u := u) E' F',
      Stable (u := u) (v := v) E' F' ∧ VFF (v := v) F' ∧ VES (v := v) E' F'] := by
  tfae_have 1 → 2 := fun h =>
    ⟨stable_of_corresp adj E' F' h, ((condition1 adj E').2 h.1).1, ((condition2 adj F').2 h.2.1).1⟩
  tfae_have 2 → 1 := fun ⟨hs, hu, hv⟩ =>
    corresp_of adj E' F' hs (unit_of_stable adj E' F' hs hu) (counit_of_stable adj E' F' hs hv)
  tfae_have 1 → 3 := fun h =>
    ⟨stable_of_corresp adj E' F' h, ((condition1 adj E').2 h.1).1, fun P hP => (h.2.2.1 P).1 hP⟩
  tfae_have 3 → 1 := by
    rintro ⟨hs, hu, hes⟩
    have hη := unit_of_stable adj E' F' hs hu
    refine corresp_of adj E' F' hs hη fun P hP => ?_
    obtain ⟨Y, hY, ⟨e⟩⟩ := hes P hP
    exact (F0 adj).prop_of_iso e (u_mem_F0 adj (hη Y hY))
  tfae_have 1 → 4 := fun h =>
    ⟨stable_of_corresp adj E' F' h, ((condition2 adj F').2 h.2.1).1, fun Y hY => (h.2.2.2 Y).1 hY⟩
  tfae_have 4 → 1 := by
    rintro ⟨hs, hv, hes⟩
    have hε := counit_of_stable adj E' F' hs hv
    refine corresp_of adj E' F' hs (fun Y hY => ?_) hε
    obtain ⟨P, hP, ⟨e⟩⟩ := hes Y hY
    exact (E0 adj).prop_of_iso e (v_mem_E0 adj (hε P hP))
  tfae_finish

/-- **Page 3, c), the bijection.** For `E'` strictly full satisfying (1), the
subcategory `α(E') = \overline{u(E')}` satisfies (2), and `β(α(E')) = E'`. -/
theorem beta_alpha (h : ∀ Y, E' Y → IsIso (adj.unit.app Y)) :
    (∀ P, (∃ Y, E' Y ∧ Nonempty (u.obj Y ≅ P)) → IsIso (adj.counit.app P)) ∧
      ∀ Y, E' Y ↔ ∃ P, (∃ Y', E' Y' ∧ Nonempty (u.obj Y' ≅ P)) ∧ Nonempty (v.obj P ≅ Y) := by
  refine ⟨fun P ⟨Y, hY, ⟨e⟩⟩ => (F0 adj).prop_of_iso e (u_mem_F0 adj (h Y hY)),
    fun Y => ⟨fun hY => ?_, ?_⟩⟩
  · have := h Y hY
    exact ⟨u.obj Y, ⟨Y, hY, ⟨Iso.refl _⟩⟩, ⟨(asIso (adj.unit.app Y)).symm⟩⟩
  · rintro ⟨P, ⟨Y', hY', ⟨e⟩⟩, ⟨e'⟩⟩
    have := h Y' hY'
    exact E'.prop_of_iso (asIso (adj.unit.app Y') ≪≫ v.mapIso e ≪≫ e') hY'

/-- Dually, for `F'` strictly full satisfying (2), `β(F') = \overline{v(F')}`
satisfies (1), and `α(β(F')) = F'`. -/
theorem alpha_beta (h : ∀ P, F' P → IsIso (adj.counit.app P)) :
    (∀ Y, (∃ P, F' P ∧ Nonempty (v.obj P ≅ Y)) → IsIso (adj.unit.app Y)) ∧
      ∀ P, F' P ↔ ∃ Y, (∃ P', F' P' ∧ Nonempty (v.obj P' ≅ Y)) ∧ Nonempty (u.obj Y ≅ P) := by
  refine ⟨fun Y ⟨P, hP, ⟨e⟩⟩ => (E0 adj).prop_of_iso e (v_mem_E0 adj (h P hP)),
    fun P => ⟨fun hP => ?_, ?_⟩⟩
  · have := h P hP
    exact ⟨v.obj P, ⟨P, hP, ⟨Iso.refl _⟩⟩, ⟨asIso (adj.counit.app P)⟩⟩
  · rintro ⟨Y, ⟨P', hP', ⟨e⟩⟩, ⟨e'⟩⟩
    have := h P' hP'
    exact F'.prop_of_iso ((asIso (adj.counit.app P')).symm ≪≫ u.mapIso e ≪≫ e') hP'

end FiveConditions

section Reflective

/-! ### Pages 4–5: `E₀` reflective, `F₀` coreflective, and what they preserve -/

/-- **Page 5, condition 1).** `Im v ⊂ E₀` and `Im u ⊂ F₀` is idempotency: it is
equivalent to either half alone (`idempotent_tfae`). -/
theorem condition1_p5_iff :
    ((∀ P, E0 adj (v.obj P)) ∧ ∀ X, F0 adj (u.obj X)) ↔ ∀ P, IsIso (adj.unit.app (v.obj P)) :=
  condition2_iff adj

/-- The page's `v₀ ∘ u'`: `X ↦ vu(X)`, landing in `E₀` once `Im u ⊂ F₀`. -/
def reflector0 (hu : ∀ X, F0 adj (u.obj X)) : E ⥤ (E0 adj).FullSubcategory :=
  (E0 adj).lift (u ⋙ v) fun X => v_mem_E0 adj (hu X)

/-- **Page 5.** If `Im u ⊂ F₀`, the inclusion `E₀ ⊂ E` has the left adjoint
`v₀ ∘ u'`: `E₀` is reflective in `E`. -/
noncomputable def reflectorAdj (hu : ∀ X, F0 adj (u.obj X)) :
    reflector0 adj hu ⊣ (E0 adj).ι where
  unit := { app := adj.unit.app, naturality := fun _ _ f => adj.unit.naturality f }
  counit :=
    { app := fun Y => (E0 adj).homMk (unitIso0 adj Y).inv
      naturality := fun Y Y' f => by
        apply ObjectProperty.hom_ext
        dsimp [reflector0]
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        simp }
  left_triangle_components X := by
    have h := ((idempotent_tfae adj).out 3 1).1 hu
    apply ObjectProperty.hom_ext
    dsimp [reflector0]
    rw [Iso.comp_inv_eq, vu_unit_eq adj h]
    simp
  right_triangle_components Y := (unitIso0 adj Y).hom_inv_id

/-- **The preservation of colimits.** The reflector `E ⥤ E₀` preserves all
colimits. -/
theorem reflector0_preservesColimits (hu : ∀ X, F0 adj (u.obj X)) :
    Limits.PreservesColimitsOfSize (reflector0 adj hu) :=
  (reflectorAdj adj hu).leftAdjoint_preservesColimits

/-- The inclusion `E₀ ⊂ E` preserves all limits. -/
theorem E0_ι_preservesLimits (hu : ∀ X, F0 adj (u.obj X)) :
    Limits.PreservesLimitsOfSize (E0 adj).ι :=
  (reflectorAdj adj hu).rightAdjoint_preservesLimits

/-- `E₀` has the colimits `E` has, computed by reflecting those of `E`. -/
theorem E0_hasColimits (hu : ∀ X, F0 adj (u.obj X)) [Limits.HasColimitsOfSize.{v₁, u₁} E] :
    Limits.HasColimitsOfSize.{v₁, u₁} (E0 adj).FullSubcategory :=
  let _ : Reflective (E0 adj).ι := { L := reflector0 adj hu, adj := reflectorAdj adj hu }
  hasColimits_of_reflective (E0 adj).ι

/-- **Page 5, condition 4), first half.** The reflector `u₁ : E ⥤ E₀` is a
localization (« passage à catégorie des fractions »), at the arrows it inverts. -/
theorem reflector0_isLocalization (hu : ∀ X, F0 adj (u.obj X)) :
    (reflector0 adj hu).IsLocalization
      ((MorphismProperty.isomorphisms _).inverseImage (reflector0 adj hu)) :=
  (reflectorAdj adj hu).isLocalization

/-- **Page 5, condition 4), second half.** `β = ι ∘ u₀ : E₀ ⥤ F` is fully faithful. -/
noncomputable def beta0FullyFaithful : (u0 adj ⋙ (F0 adj).ι).FullyFaithful :=
  (fixedEquiv adj).fullyFaithfulFunctor.comp (F0 adj).fullyFaithfulι

/-- **Page 5, condition 4).** If `Im u ⊂ F₀`, then `u ≅ β ∘ u₁`, with `u₁` the
localization `E ⥤ E₀` and `β : E₀ ⥤ F` fully faithful. -/
noncomputable def condition4 (hu : ∀ X, F0 adj (u.obj X)) :
    reflector0 adj hu ⋙ u0 adj ⋙ (F0 adj).ι ≅ u :=
  NatIso.ofComponents (fun X => @asIso _ _ _ _ (adj.counit.app (u.obj X)) (hu X))
    (fun f => adj.counit.naturality (u.map f))

/-- The page's `u₀ ∘ v'`: `P ↦ uv(P)`, landing in `F₀` once `Im v ⊂ E₀`. -/
def coreflector0 (hv : ∀ P, E0 adj (v.obj P)) : F ⥤ (F0 adj).FullSubcategory :=
  (F0 adj).lift (v ⋙ u) fun P => u_mem_F0 adj (hv P)

/-- **Page 4.** If `Im v ⊂ E₀`, the inclusion `F₀ ⊂ F` has the right adjoint
`u₀ ∘ v'`: `F₀` is coreflective in `F`. -/
noncomputable def coreflectorAdj (hv : ∀ P, E0 adj (v.obj P)) :
    (F0 adj).ι ⊣ coreflector0 adj hv where
  unit :=
    { app := fun P => (F0 adj).homMk (counitIso0 adj P).inv
      naturality := fun P P' f => by
        apply ObjectProperty.hom_ext
        dsimp [coreflector0]
        rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
        simp }
  counit := { app := adj.counit.app, naturality := fun _ _ f => adj.counit.naturality f }
  left_triangle_components P := (counitIso0 adj P).inv_hom_id
  right_triangle_components P := by
    have h := ((idempotent_tfae adj).out 1 3).1 hv
    apply ObjectProperty.hom_ext
    dsimp [coreflector0]
    rw [Iso.inv_comp_eq, uv_counit_eq adj h]
    simp

/-- `η_Y` as an isomorphism, for `Y` with `η_Y` invertible. -/
noncomputable def isoOfE0 {Y : E} (h : E0 adj Y) : Y ≅ v.obj (u.obj Y) :=
  @asIso _ _ _ _ (adj.unit.app Y) h

@[simp] theorem isoOfE0_hom {Y : E} (h : E0 adj Y) : (isoOfE0 adj h).hom = adj.unit.app Y := rfl

/-- **Page 5, condition 4').** If `Im v ⊂ E₀`, then `v ≅ α ∘ v₁`, with `v₁` the
coreflector `F ⥤ F₀` followed by `v₀`, and `α : E₀ ⊂ E`. With `condition4`, this
is the page's `u = β u₀ α'`, `v = α v₀ β'` for an idempotent adjunction. -/
noncomputable def condition4' (hv : ∀ P, E0 adj (v.obj P)) :
    coreflector0 adj hv ⋙ v0 adj ⋙ (E0 adj).ι ≅ v :=
  NatIso.ofComponents (fun P => (isoOfE0 adj (hv P)).symm)
    (fun f => by
      dsimp [coreflector0, v0]
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      simp)

/-- **Page 5, condition 3).** For an idempotent adjunction (`Im v ⊂ E₀`), the
inclusion `E₀ ⊂ E` has a left adjoint and `F₀ ⊂ F` a right adjoint. -/
theorem condition3_p5 (hv : ∀ P, E0 adj (v.obj P)) :
    (E0 adj).ι.IsRightAdjoint ∧ (F0 adj).ι.IsLeftAdjoint :=
  ⟨⟨_, ⟨reflectorAdj adj ((idempotent_tfae adj).out 1 3 |>.1 hv)⟩⟩, ⟨_, ⟨coreflectorAdj adj hv⟩⟩⟩

/-- The coreflector `F ⥤ F₀` preserves all limits. -/
theorem coreflector0_preservesLimits (hv : ∀ P, E0 adj (v.obj P)) :
    Limits.PreservesLimitsOfSize (coreflector0 adj hv) :=
  (coreflectorAdj adj hv).rightAdjoint_preservesLimits

/-- The inclusion `F₀ ⊂ F` preserves all colimits. -/
theorem F0_ι_preservesColimits (hv : ∀ P, E0 adj (v.obj P)) :
    Limits.PreservesColimitsOfSize (F0 adj).ι :=
  (coreflectorAdj adj hv).leftAdjoint_preservesColimits

/-- `F₀` has the limits `F` has, computed by coreflecting those of `F`. -/
theorem F0_hasLimits (hv : ∀ P, E0 adj (v.obj P)) [Limits.HasLimitsOfSize.{v₂, u₂} F] :
    Limits.HasLimitsOfSize.{v₂, u₂} (F0 adj).FullSubcategory :=
  let _ : Coreflective (F0 adj).ι := { R := coreflector0 adj hv, adj := coreflectorAdj adj hv }
  hasLimits_of_coreflective (F0 adj).ι

end Reflective

section Local

/-! ### Reflective subcategories and local objects (pages 6–7)

`α : E₁ ⥤ E` fully faithful with left adjoint `α'`. `Σ` is the class of arrows
that `α'` inverts. -/

variable {E₁ : Type u₂} [Category.{v₂} E₁] {α : E₁ ⥤ E} {α' : E ⥤ E₁} (adj' : α' ⊣ α)
  [α.Full] [α.Faithful]

/-- The class `Σ` of arrows inverted by the reflector. -/
def Sigma' : MorphismProperty E := fun _ _ f => IsIso (α'.map f)

include adj'

/-- **Page 7.** `f ∈ Σ` if and only if `Hom(Y, αZ₁) → Hom(X, αZ₁)` is bijective
for every `Z₁ ∈ E₁`. (mathlib: `ObjectProperty.isLocal_iff_isIso_map`.) -/
theorem sigma_iff {X Y : E} (f : X ⟶ Y) :
    Sigma' (α' := α') f ↔
      ∀ Z₁ : E₁, Function.Bijective (fun g : Y ⟶ α.obj Z₁ => f ≫ g) := by
  rw [Sigma', ← ObjectProperty.isLocal_iff_isIso_map adj' f]
  exact ⟨fun h Z₁ => h _ ⟨Z₁, rfl⟩, fun h _ ⟨Z₁, hZ⟩ => hZ ▸ h Z₁⟩

/-- **« Or c'est vrai sauf erreur… »** A `Σ`-local object is in the essential
image of `α`. -/
theorem local_mem_essImage {ξ : E} (hξ : (Sigma' (α' := α')).isLocal ξ) : α.essImage ξ := by
  let η := adj'.unit.app ξ
  have hη : Sigma' (α' := α') η :=
    (ObjectProperty.isLocal_iff_isIso_map adj' η).1 (ObjectProperty.isLocal_adj_unit_app adj' ξ)
  -- `η` has a retraction `r`, because `ξ` is local …
  obtain ⟨r, hr⟩ := (hξ η hη).2 (𝟙 ξ)
  have hr' : η ≫ r = 𝟙 ξ := hr
  -- … and `r` is also a section, because `α α' ξ` is local for `η`.
  have hrη : r ≫ η = 𝟙 _ := by
    apply (ObjectProperty.isLocal_adj_unit_app adj' ξ _ ⟨α'.obj ξ, rfl⟩).1
    show η ≫ r ≫ η = η ≫ 𝟙 _
    rw [← Category.assoc, hr']
    simp
  exact ⟨α'.obj ξ, ⟨{ hom := r, inv := η, hom_inv_id := hrη, inv_hom_id := hr' }⟩⟩

/-- The `Σ`-local objects are exactly the essential image of `α`. -/
theorem local_iff_mem_essImage (ξ : E) :
    (Sigma' (α' := α')).isLocal ξ ↔ α.essImage ξ := by
  refine ⟨local_mem_essImage adj', ?_⟩
  rintro ⟨Z₁, ⟨e⟩⟩
  have : (Sigma' (α' := α')).isLocal (α.obj Z₁) := fun X Y f hf => (sigma_iff adj' f).1 hf Z₁
  exact (Sigma' (α' := α')).isLocal.prop_of_iso e this

end Local

section Descent

/-! ### Page 6: the descent of adjoints

`α : E₁ ⥤ E` fully faithful with left adjoint `α'`. The page asks whether, for
`β : E₁ ⥤ F` fully faithful such that `u = β ∘ α'` has a right adjoint, `β` has
one, and reduces it to a representability question. Here all hom-sets live in
the same universe, as representability requires. -/

variable {E₁ : Type u₂} [Category.{v₁} E₁] {α : E₁ ⥤ E} {α' : E ⥤ E₁} (adj' : α' ⊣ α)
  [α.Full] [α.Faithful]

include adj'

/-- **Page 6, the reduced question.** A presheaf `ψ` on `E₁` such that
`ψ ∘ α'` is representable is representable. -/
theorem descent (ψ : E₁ᵒᵖ ⥤ Type v₁) [(α'.op ⋙ ψ).IsRepresentable] : ψ.IsRepresentable := by
  obtain ⟨ξ, ⟨R⟩⟩ := (inferInstance : (α'.op ⋙ ψ).IsRepresentable).has_representation
  have hloc : (Sigma' (α' := α')).isLocal ξ := fun X Y f hf => by
    have : IsIso (α'.map f) := hf
    have e : (fun g : Y ⟶ ξ => f ≫ g) =
        ⇑(R.homEquiv.trans ((ψ.mapIso (asIso (α'.map f)).op).toEquiv.trans R.homEquiv.symm)) := by
      funext g
      apply R.homEquiv.injective
      simp [R.homEquiv_comp]
    rw [e]
    exact Equiv.bijective _
  obtain ⟨ξ₁, ⟨e⟩⟩ := local_mem_essImage adj' hloc
  let hα := Functor.FullyFaithful.ofFullyFaithful α
  let c : ∀ Z : E₁, ψ.obj (Opposite.op Z) ≃ ψ.obj (Opposite.op (α'.obj (α.obj Z))) :=
    fun Z => (ψ.mapIso (asIso (adj'.counit.app Z)).op).toEquiv
  have hc : ∀ Z x, c Z x = ψ.map (adj'.counit.app Z).op x := fun _ _ => rfl
  exact Functor.RepresentableBy.isRepresentable
    { homEquiv := fun {Z} => hα.homEquiv.trans (e.homToEquiv.trans (R.homEquiv.trans (c Z).symm))
      homEquiv_comp := fun {Z Z'} f g => by
        apply (c Z).injective
        simp only [Equiv.trans_apply]
        rw [Equiv.apply_symm_apply]
        have h1 : e.homToEquiv (hα.homEquiv (f ≫ g)) = α.map f ≫ e.homToEquiv (hα.homEquiv g) := by
          simp [Iso.homToEquiv]
        rw [h1, R.homEquiv_comp]
        generalize R.homEquiv (e.homToEquiv (hα.homEquiv g)) = y
        obtain ⟨w, rfl⟩ := (c Z').surjective y
        rw [Equiv.symm_apply_apply, hc, hc]
        change ψ.map (α'.map (α.map f)).op (ψ.map (adj'.counit.app Z').op w) = _
        simp only [← Functor.map_comp_apply, ← op_comp]
        congr 3
        exact congrArg Quiver.Hom.op (adj'.counit.naturality f) }

/-- **Page 6, the question.** If `β ∘ α'` has a right adjoint, so has `β`.
The full faithfulness of `β`, which the page assumes, is not used. -/
theorem descent_isLeftAdjoint {G : Type*} [Category.{v₁} G] (β : E₁ ⥤ G)
    [(α' ⋙ β).IsLeftAdjoint] : β.IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  funext P
  simp only [Pi.top_apply, Prop.top_eq_true, eq_iff_iff, iff_true]
  have : (α'.op ⋙ (β.op ⋙ yoneda.obj P)).IsRepresentable :=
    Functor.rightAdjointObjIsDefined_of_adjunction (Adjunction.ofIsLeftAdjoint (α' ⋙ β)) P
  exact descent adj' (β.op ⋙ yoneda.obj P)

end Descent

/-! ## Pages 11–12: inverses of an invertible object and the sign `ε(L)`

Page 12 takes an invertible object `L` of a symmetric monoidal category `C`
with an inverse `L'`, `φ_{L,L'} : L ⊗ L' ≅ 𝟙`, and compares two trivialisations
of `L' ⊗ L`: `φ_{L',L} = φ_{L,L'} ∘ s_{L',L}`, obtained through the symmetry,
and `ψ_{L',L}`, defined by the triangle identity
`φ_{L,L'} ⊗ id_L = id_L ⊗ ψ_{L',L} : L ⊗ L' ⊗ L → L`.
« Relations entre `φ_{L',L}` et `ψ_{L',L}` ? » The reading's answer: they
differ by the sign `ε(L) ∈ Aut(𝟙)` by which the symmetry acts on `L ⊗ L`.

* `scalar e X` — the action of `e : 𝟙 ⟶ 𝟙` on an object, `λ⁻¹ ≫ e ▷ X ≫ λ`;
  it is natural in `X` (`scalar_naturality`).
* `psi`, `psi_triangle`, `psi_unique` — `ψ_{L',L}` exists, is an isomorphism, and
  is the only morphism satisfying the triangle identity (tensoring with `L` is
  an equivalence, `tensorLeftEquivOfInverse`).
* `epsilon φ := ψ⁻¹ ≫ φ_{L',L}`, and the answer to the page's question:
  `braiding_self_eq_scalar` — `s_{L,L} = ε · id_{L⊗L}`; `phiSwap_eq_iff` — for any
  scalar `e`, `φ_{L',L} = e · ψ_{L',L}` iff `s_{L,L} = e · id_{L⊗L}`; hence
  `phiSwap_eq_scalar_comp` : `φ_{L',L} = ε(L) · ψ_{L',L}`.
* `epsilon_eq_of_inverse` — `ε(L)` depends on `L` only, not on the inverse
  `(L', φ)` chosen; `epsilon_mul_self` — `ε(L)² = 1`.
-/

section Contractions

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- The action of a scalar `e ∈ End(𝟙)` on an object `X`. -/
def scalar (e : 𝟙_ C ⟶ 𝟙_ C) (X : C) : X ⟶ X :=
  (λ_ X).inv ≫ e ▷ X ≫ (λ_ X).hom

/-- Scalars commute with every morphism. -/
@[reassoc]
lemma scalar_naturality (e : 𝟙_ C ⟶ 𝟙_ C) {X Y : C} (f : X ⟶ Y) :
    f ≫ scalar e Y = scalar e X ≫ f := by
  simp only [scalar, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    Category.assoc, leftUnitor_naturality]

lemma scalar_tensor (e : 𝟙_ C ⟶ 𝟙_ C) (X Y : C) :
    scalar e (X ⊗ Y) = scalar e X ▷ Y := by
  simp [scalar]

lemma scalar_comp (e e' : 𝟙_ C ⟶ 𝟙_ C) (X : C) :
    scalar (e ≫ e') X = scalar e X ≫ scalar e' X := by
  simp [scalar]

lemma scalar_id (X : C) : scalar (𝟙 (𝟙_ C)) X = 𝟙 X := by
  simp [scalar]

lemma scalar_unit (e : 𝟙_ C ⟶ 𝟙_ C) : scalar e (𝟙_ C) = e := by
  rw [scalar, unitors_equal]
  simp [unitors_inv_equal]

/-- If `Y ⊗ X ≅ 𝟙` and `X ⊗ Y ≅ 𝟙`, tensoring on the left with `X` is an
equivalence, with quasi-inverse tensoring with `Y`. -/
def tensorLeftEquivOfInverse {X Y : C} (i : Y ⊗ X ≅ 𝟙_ C) (j : X ⊗ Y ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft X) (tensorLeft Y)
    (NatIso.ofComponents (fun Z => (λ_ Z).symm ≪≫ whiskerRightIso i.symm Z ≪≫ α_ Y X Z)
      (by
        intro _ _ f
        dsimp
        simp only [whiskerRightIso_hom, Iso.symm_hom, Category.assoc]
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
        simp))
    (NatIso.ofComponents (fun Z => (α_ X Y Z).symm ≪≫ whiskerRightIso j Z ≪≫ λ_ Z)
      (by
        intro _ _ f
        dsimp
        simp only [whiskerRightIso_hom, Category.assoc]
        rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
        simp))

variable [SymmetricCategory C] {L L' : C}

open BraidedCategory

/-- `φ_{L',L} = φ_{L,L'} ∘ s_{L',L}`, the trivialisation of `L' ⊗ L` through the
symmetry (page 12). -/
def phiSwap (φ : L ⊗ L' ≅ 𝟙_ C) : L' ⊗ L ≅ 𝟙_ C := β_ L' L ≪≫ φ

/-- Tensoring with an invertible `L` is fully faithful. -/
def fullyFaithfulL (φ : L ⊗ L' ≅ 𝟙_ C) : (tensorLeft L).FullyFaithful :=
  (tensorLeftEquivOfInverse (phiSwap φ) φ).fullyFaithfulFunctor

/-- Tensoring with the inverse `L'` is fully faithful. -/
def fullyFaithfulL' (φ : L ⊗ L' ≅ 𝟙_ C) : (tensorLeft L').FullyFaithful :=
  (tensorLeftEquivOfInverse φ (phiSwap φ)).fullyFaithfulFunctor

/-- `ψ_{L',L} : L' ⊗ L ≅ 𝟙`, defined by the triangle identity
`φ_{L,L'} ⊗ id_L = id_L ⊗ ψ_{L',L}` (page 12). -/
def psi (φ : L ⊗ L' ≅ 𝟙_ C) : L' ⊗ L ≅ 𝟙_ C :=
  (fullyFaithfulL φ).preimageIso
    ((α_ L L' L).symm ≪≫ whiskerRightIso φ L ≪≫ λ_ L ≪≫ (ρ_ L).symm)

/-- The triangle identity defining `ψ_{L',L}`, with associator and unitors. -/
lemma psi_triangle (φ : L ⊗ L' ≅ 𝟙_ C) :
    φ.hom ▷ L ≫ (λ_ L).hom = (α_ L L' L).hom ≫ L ◁ (psi φ).hom ≫ (ρ_ L).hom := by
  simp [show L ◁ (psi φ).hom = (α_ L L' L).inv ≫ φ.hom ▷ L ≫ (λ_ L).hom ≫ (ρ_ L).inv from
    (fullyFaithfulL φ).map_preimage _]

/-- `ψ_{L',L}` is the only morphism satisfying the triangle identity. -/
lemma psi_unique (φ : L ⊗ L' ≅ 𝟙_ C) (ψ' : L' ⊗ L ⟶ 𝟙_ C)
    (h : φ.hom ▷ L ≫ (λ_ L).hom = (α_ L L' L).hom ≫ L ◁ ψ' ≫ (ρ_ L).hom) :
    ψ' = (psi φ).hom := by
  apply (fullyFaithfulL φ).map_injective
  change L ◁ ψ' = L ◁ (psi φ).hom
  simpa using h.symm.trans (psi_triangle φ)

lemma whiskerRight_injective {Z : C} (hZ : (tensorLeft Z).FullyFaithful) {X Y : C}
    {f g : X ⟶ Y} (h : f ▷ Z = g ▷ Z) : f = g :=
  hZ.map_injective (by
    change Z ◁ f = Z ◁ g
    rw [← cancel_epi (β_ X Z).hom, ← braiding_naturality_left, h, braiding_naturality_left])

/-- `ε := ψ_{L',L}⁻¹ ≫ φ_{L',L} ∈ Aut(𝟙)`; `braiding_self_eq_scalar` shows that
it is the sign of the symmetry of `L ⊗ L`. -/
def epsilon (φ : L ⊗ L' ≅ 𝟙_ C) : 𝟙_ C ⟶ 𝟙_ C := (psi φ).inv ≫ (phiSwap φ).hom

lemma whiskerLeft_scalar_rightUnitor (e : 𝟙_ C ⟶ 𝟙_ C) (X : C) :
    X ◁ e ≫ (ρ_ X).hom = (ρ_ X).hom ≫ scalar e X := by
  have := braiding_naturality_right X e
  rw [← braiding_leftUnitor, Category.assoc, reassoc_of% this]
  simp only [scalar, Iso.hom_inv_id_assoc]

/-- **Page 12, the answer.** The symmetry of `L ⊗ L` is the scalar `ε`:
`s_{L,L} = ε · id_{L⊗L}`. The proof follows the page's naturality square: the
symmetry `s_{L, L ⊗ L'}` is natural against `φ_{L,L'}`, the hexagon splits it as
`(s_{L,L} ⊗ L') ; (L ⊗ s_{L,L'})`, the triangle identity replaces `φ ⊗ L` by
`L ⊗ ψ`, and the isomorphism `L ⊗ (ψ ∘ s_{L,L'})` cancels. -/
theorem braiding_self_eq_scalar (φ : L ⊗ L' ≅ 𝟙_ C) :
    (β_ L L).hom = scalar (epsilon φ) (L ⊗ L) := by
  set ψ := psi φ
  have A : L ◁ φ.hom ≫ (ρ_ L).hom = (β_ L (L ⊗ L')).hom ≫ φ.hom ▷ L ≫ (λ_ L).hom := by
    rw [← braiding_leftUnitor, ← braiding_naturality_right_assoc]
  have hφ : φ.hom = ((β_ L L').hom ≫ ψ.hom) ≫ epsilon φ := by
    simp [epsilon, phiSwap]
  rw [psi_triangle φ, hφ, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_scalar_rightUnitor, ← Category.assoc, ← Category.assoc,
    scalar_naturality, braiding_tensor_right_hom] at A
  have B : scalar (epsilon φ) (L ⊗ (L ⊗ L')) =
      (α_ L L L').inv ≫ (β_ L L).hom ▷ L' ≫ (α_ L L L').hom := by
    rw [← cancel_mono (L ◁ ((β_ L L').hom ≫ ψ.hom) ≫ (ρ_ L).hom), A]
    simp [ψ]
  apply whiskerRight_injective (fullyFaithfulL' φ)
  rw [← scalar_tensor, ← Iso.hom_inv_id_assoc (α_ L L L') (scalar _ _),
    scalar_naturality (epsilon φ) (α_ L L L').inv, B]
  simp

/-- A scalar is determined by its action on `L ⊗ L`, `L` invertible. -/
lemma scalar_injective (φ : L ⊗ L' ≅ 𝟙_ C) {e e' : 𝟙_ C ⟶ 𝟙_ C}
    (h : scalar e (L ⊗ L) = scalar e' (L ⊗ L)) : e = e' := by
  rw [scalar_tensor, scalar_tensor] at h
  refine whiskerRight_injective (fullyFaithfulL φ) ?_
  simpa [scalar] using congrArg (fun f => (λ_ L).hom ≫ f ≫ (λ_ L).inv)
    (whiskerRight_injective (fullyFaithfulL φ) h)

/-- **Page 12, « Relations entre `φ_{L',L}` et `ψ_{L',L}` ? »** For a scalar `e`,
`φ_{L',L} = e · ψ_{L',L}` if and only if the symmetry acts on `L ⊗ L` by `e`. -/
theorem phiSwap_eq_iff (φ : L ⊗ L' ≅ 𝟙_ C) (e : 𝟙_ C ⟶ 𝟙_ C) :
    (phiSwap φ).hom = (psi φ).hom ≫ e ↔ (β_ L L).hom = scalar e (L ⊗ L) := by
  constructor
  · intro h
    rw [show e = epsilon φ by simp [epsilon, h]]
    exact braiding_self_eq_scalar φ
  · intro h
    rw [scalar_injective φ (h.symm.trans (braiding_self_eq_scalar φ))]
    simp [epsilon]

/-- `φ_{L',L} = ε(L) · ψ_{L',L}`, the scalar acting on `L' ⊗ L`. -/
theorem phiSwap_eq_scalar_comp (φ : L ⊗ L' ≅ 𝟙_ C) :
    (phiSwap φ).hom = scalar (epsilon φ) (L' ⊗ L) ≫ (psi φ).hom := by
  rw [← scalar_naturality, scalar_unit]
  simp [epsilon]

/-- `ε(L)` does not depend on the inverse `(L', φ)` chosen. -/
theorem epsilon_eq_of_inverse {L₁ L₂ : C} (φ₁ : L ⊗ L₁ ≅ 𝟙_ C) (φ₂ : L ⊗ L₂ ≅ 𝟙_ C) :
    epsilon φ₁ = epsilon φ₂ :=
  scalar_injective φ₁ ((braiding_self_eq_scalar φ₁).symm.trans (braiding_self_eq_scalar φ₂))

/-- `ε(L)² = 1`. -/
theorem epsilon_mul_self (φ : L ⊗ L' ≅ 𝟙_ C) : epsilon φ ≫ epsilon φ = 𝟙 _ :=
  scalar_injective φ (by
    rw [scalar_comp, ← braiding_self_eq_scalar, scalar_id]
    exact SymmetricCategory.symmetry L L)

end Contractions

end Grothendieck.Folder161_1
