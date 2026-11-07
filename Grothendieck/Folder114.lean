module

public import Mathlib
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Data.ZMod.Defs

@[expose] public section


/-!
# Folder 114: fundamental localisers, `W₀`, and the minimal one

The modernised reading `transcripts/114/114.modern.tex` (page 3, the typescript
page 350 of *Pursuing Stacks*) fixes its vocabulary as follows:

> Un *localisateur fondamental* `W` est une classe de foncteurs entre petites
> catégories […] : elle est faiblement saturée, elle contient les foncteurs
> `A → e` pour toute `A` ayant un objet final, et elle vérifie une condition du
> type « théorème A » de Quillen.
>
> Une petite catégorie `A` est *`W`-asphérique* si `A → e` appartient à `W` ;
> elle est *totalement `W`-asphérique* si de plus le produit `a × b` de deux
> représentables est `W`-asphérique dans `Â`. Un objet `X` de `Â` est
> *`0`-connexe* si […] la catégorie `A_{/X}` est non vide et connexe.

and argues Proposition 4 through the sandwich

> Tout localisateur fondamental `W` vérifie `W_∞ ⊆ W ⊆ W₀`, où `W₀` est le
> localisateur fondamental le plus grossier. […] `W₀` est le localisateur pour
> lequel un foncteur est une équivalence dès qu'il induit une bijection sur les
> composantes connexes : `W₀`-asphérique et `0`-connexe sont le même mot.

(its footnote says the identification of `W₀` is the edition's, not the page's).

The reading's definition is loose, so `LocalisateurFondamental` takes the
standard axioms (Grothendieck's LA–LC as Maltsiniotis states them — recalled,
not checked against a text): LA weak saturation (identities, two-out-of-three,
and `r ∘ i = 1`, `i ∘ r ∈ W` ⟹ `r ∈ W`), LB `A → e ∈ W` when `A` has a final
object, LC Quillen's theorem A over a base (`u : A → B` over `C`, all
`A/c → B/c` in `W` ⟹ `u ∈ W`). "Small category" means objects and arrows in
`Type u`.

## What is proved

* `W₀_localisateurFondamental`: the functors inducing a bijection on `π₀` form a
  fundamental localiser — the reading's identification of `W₀` holds as far as
  it says `W₀` is one.
* `aspherique_W₀_iff`: `W₀`-aspheric ⟺ `0`-connected (non-empty and connected).
* `totalementAspherique_W₀_iff`: totally `W₀`-aspheric ⟺ condition (iii) of
  Proposition 4 (including the page's « (iii) implies that `A` is
  `0`-connected »).
* `Wmin`, `Wmin_localisateurFondamental`, `Wmin_inclus`: the **minimal
  fundamental localiser** exists — the intersection of all of them is one, and
  it is contained in every one. This is `W_∞` *by definition* («  le
  localisateur fondamental le plus fin »); that it is the class of usual weak
  homotopy equivalences is Cisinski's theorem and is **not** formalised (mathlib
  has no weak equivalences of small categories to compare with).
* `proposition4_i_ii`: (i) ⇒ (ii) for every fundamental localiser `W`
  (`W_∞ ⊆ W`), and `proposition4_ii_iii`: (ii) ⇒ (iii) *under the hypothesis
  `W ⊆ W₀`*.

## What the formalisation finds

**The right-hand inclusion `W ⊆ W₀` is false as the reading states it**, and
`W₀` is *not* the coarsest fundamental localiser:
* the class of all functors is a fundamental localiser not contained in `W₀`
  (`Wtrivial_not_inclus_W₀`), and so, less trivially, is
* `W₋₁`, the functors `A → B` with `A` empty iff `B` empty
  (`Wmoins1_localisateurFondamental`, `Wmoins1_not_inclus_W₀`): the functor from
  the two-point discrete category to `e` is in `W₋₁`, not in `W₀`.

Proposition 4 as the reading states it (for *every* fundamental localiser) then
fails in its **(ii) ⇒ (iii) and (ii) ⇒ (i)** directions, not only in the
(iii) ⇒ (i) direction that the literature refutes: for `W = W₋₁`, the one-object
category `B(ℤ/2)` is totally `W₋₁`-aspheric but `∗ × ∗` is not `0`-connected —
the diagonal action of `ℤ/2` on `ℤ/2 × ℤ/2` has two orbits
(`contreExemple_proposition4`), so it is not totally `W_∞`-aspheric either
(`contreExemple_proposition4_i_ii`). (For the trivial localiser, the empty
category is already a counterexample to (ii) ⇒ (iii).) The reading's argument
goes through once `W ⊆ W₀` is assumed (`proposition4_ii_iii`), which is the
hypothesis to add.

## Not formalised

* That `W_∞` is the class of usual weak equivalences (Cisinski 2004), which the
  reading and the page rely on.
* (iii) ⇒ (i) of Proposition 4, which the reading presents as true and the
  literature refutes (the category of cubes); not attempted, and nothing here
  depends on it.
* Pages 1, 2, 4 and 5 (the programme, the list of test categories, the NB on
  aspheric functors, modelisers and `M_as`): outside the #26 row.

What this certifies is that the reading holds together where it does, not that
it is what the page says (issue #26).
-/

namespace Grothendieck.Folder114

open CategoryTheory Limits Function

universe u

/-- A class of functors between small categories (objects and arrows in
`Type u`). -/
abbrev ClasseDeFoncteurs : Type (u + 1) :=
  ∀ ⦃A B : Type u⦄ [Category.{u} A] [Category.{u} B], (A ⥤ B) → Prop

/-- A *localisateur fondamental*: axioms LA (weak saturation: `id_mem`,
two-out-of-three `comp_mem`, `of_comp_left`, `of_comp_right`, and `retract`),
LB (`final`: `A → e ∈ W` when `A` has a final object) and LC (`theoremeA`: for
`v : A → B` over `w : B → C`, if every `A/c → B/c` is in `W`, then `v` is). -/
structure LocalisateurFondamental (W : ClasseDeFoncteurs.{u}) : Prop where
  id_mem : ∀ (A : Type u) [Category.{u} A], W (𝟭 A)
  comp_mem : ∀ {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (F : A ⥤ B) (G : B ⥤ C), W F → W G → W (F ⋙ G)
  of_comp_left : ∀ {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (F : A ⥤ B) (G : B ⥤ C), W F → W (F ⋙ G) → W G
  of_comp_right : ∀ {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (F : A ⥤ B) (G : B ⥤ C), W G → W (F ⋙ G) → W F
  retract : ∀ {A B : Type u} [Category.{u} A] [Category.{u} B] (i : A ⥤ B) (r : B ⥤ A),
    i ⋙ r = 𝟭 A → W (r ⋙ i) → W r
  final : ∀ (A : Type u) [Category.{u} A] [HasTerminal A], W (Functor.star.{u} A)
  theoremeA : ∀ {A B C : Type u} [Category.{u} A] [Category.{u} B] [Category.{u} C]
    (v : A ⥤ B) (w : B ⥤ C), (∀ c : C, W (CostructuredArrow.pre v w c)) → W v

/-- `W₀`: the functors inducing a bijection on connected components. -/
def W₀ : ClasseDeFoncteurs.{u} := fun _ _ _ _ F => Bijective F.mapConnectedComponents

section

variable {J K L : Type*} [Category J] [Category K] [Category L]

lemma mapCC_comp (F : J ⥤ K) (G : K ⥤ L) :
    (F ⋙ G).mapConnectedComponents = G.mapConnectedComponents ∘ F.mapConnectedComponents := by
  funext x; induction x using Quotient.inductionOn; rfl

lemma mapCC_id : (𝟭 J).mapConnectedComponents = id := by
  funext x; induction x using Quotient.inductionOn; rfl

lemma zigzag_of_injective {F : J ⥤ K} (h : Injective F.mapConnectedComponents) {j j' : J}
    (hz : Zigzag (F.obj j) (F.obj j')) : Zigzag j j' :=
  Quotient.exact (h (Quotient.sound hz))

end

lemma bijective_star (A : Type u) [Category.{u} A] [IsConnected A] :
    Bijective (Functor.star.{u} A).mapConnectedComponents :=
  ⟨fun x y _ => Quotient.inductionOn₂ x y fun a b => Quotient.sound (isPreconnected_zigzag a b),
    fun y => Quotient.inductionOn y fun _ =>
      ⟨Quotient.mk _ (Classical.arbitrary A), Quotient.sound (Zigzag.of_hom (eqToHom (by ext)))⟩⟩

theorem W₀_localisateurFondamental : LocalisateurFondamental W₀.{u} where
  id_mem A _ := (mapCC_id (J := A) ▸ bijective_id :)
  comp_mem F G hF hG := (mapCC_comp F G ▸ hG.comp hF :)
  of_comp_left F G hF hFG := (Bijective.of_comp_iff _ hF).1 (mapCC_comp F G ▸ hFG)
  of_comp_right F G hG hFG := (Bijective.of_comp_iff' hG _).1 (mapCC_comp F G ▸ hFG)
  retract i r hir hri := by
    have h1 : r.mapConnectedComponents ∘ i.mapConnectedComponents = id := by
      rw [← mapCC_comp, hir, mapCC_id]
    have h2 : Bijective (i.mapConnectedComponents ∘ r.mapConnectedComponents) :=
      mapCC_comp r i ▸ hri
    exact ⟨fun x y hxy => h2.1 (by simp only [comp_apply, hxy]), fun x => ⟨_, congrFun h1 x⟩⟩
  final A _ _ := @bijective_star A _ (isConnected_of_hasTerminal A)
  theoremeA := by
    intro A B C _ _ _ v w h
    -- for each `b`, a chosen object of `A/w(b)` over the component of `(b, 1)`
    have hs : ∀ b : B, ∃ α : CostructuredArrow (v ⋙ w) (w.obj b),
        Zigzag ((CostructuredArrow.pre v w _).obj α) (CostructuredArrow.mk (𝟙 (w.obj b))) := by
      intro b
      obtain ⟨α, hα⟩ := (h (w.obj b)).2 (Quotient.mk _ (CostructuredArrow.mk (𝟙 (w.obj b))))
      induction α using Quotient.inductionOn with | h α => exact ⟨α, Quotient.exact hα⟩
    choose α hα using hs
    let s : B → ConnectedComponents A := fun b => Quotient.mk _ (α b).left
    have hs1 : ∀ a : A, s (v.obj a) = Quotient.mk _ a := by
      intro a
      have : Zigzag (α (v.obj a)) (CostructuredArrow.mk (Y := a) (𝟙 ((v ⋙ w).obj a))) :=
        zigzag_of_injective (h _).1 (hα (v.obj a))
      exact Quotient.sound (zigzag_obj_of_zigzag (CostructuredArrow.proj _ _) this)
    have hs2 : ∀ {b b' : B} (g : b ⟶ b'), s b = s b' := by
      intro b b' g
      let T := CostructuredArrow.map (S := v ⋙ w) (w.map g)
      have z1 := zigzag_obj_of_zigzag (CostructuredArrow.map (S := w) (w.map g)) (hα b)
      have z2 : Zigzag ((CostructuredArrow.map (S := w) (w.map g)).obj
          (CostructuredArrow.mk (𝟙 (w.obj b)))) (CostructuredArrow.mk (𝟙 (w.obj b'))) :=
        Zigzag.of_hom (CostructuredArrow.homMk g (by simp))
      have z3 : Zigzag ((CostructuredArrow.pre v w _).obj (T.obj (α b)))
          ((CostructuredArrow.pre v w _).obj (α b')) := (z1.trans z2).trans (hα b').symm
      have z4 := zigzag_of_injective (h _).1 z3
      exact Quotient.sound (zigzag_obj_of_zigzag (CostructuredArrow.proj _ _) z4)
    have hs3 : ∀ {b b' : B}, Zigzag b b' → s b = s b' := by
      intro b b' hz
      induction hz with
      | refl => rfl
      | tail _ hzag ih =>
        rcases hzag with ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
        · exact ih.trans (hs2 g)
        · exact ih.trans (hs2 g).symm
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · induction x, y using Quotient.inductionOn₂ with | h a a' => ?_
      rw [← hs1, ← hs1]
      exact hs3 (Quotient.exact hxy)
    · induction y using Quotient.inductionOn with | h b =>
      exact ⟨s b, Quotient.sound (zigzag_obj_of_zigzag (CostructuredArrow.proj _ _) (hα b))⟩

/-! ### Asphericity, and `W₀` -/

/-- A small category `A` is `W`-aspheric when `A → e` is in `W`. -/
def Aspherique (W : ClasseDeFoncteurs.{u}) (A : Type u) [Category.{u} A] : Prop :=
  W (Functor.star.{u} A)

/-- `W₀`-aspheric and `0`-connected are the same word. -/
theorem aspherique_W₀_iff (A : Type u) [Category.{u} A] :
    Aspherique W₀ A ↔ IsConnected A := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    obtain ⟨x, -⟩ := hsurj (Quotient.mk _ ⟨⟨⟩⟩)
    induction x using Quotient.inductionOn with | h a => ?_
    have : Nonempty A := ⟨a⟩
    exact zigzag_isConnected fun a a' => Quotient.exact (hinj (a₁ := Quotient.mk _ a)
      (a₂ := Quotient.mk _ a') rfl)
  · exact fun _ => bijective_star A

/-- The product `a × b` of two representables in `Â`, computed objectwise:
`(a × b)(c) = Hom(c, a) × Hom(c, b)`. -/
@[simps obj]
def produitRep {A : Type u} [Category.{u} A] (a b : A) : Aᵒᵖ ⥤ Type u where
  obj c := (c.unop ⟶ a) × (c.unop ⟶ b)
  map f := TypeCat.ofHom fun x => (f.unop ≫ x.1, f.unop ≫ x.2)

@[simp]
lemma produitRep_map_apply {A : Type u} [Category.{u} A] (a b : A) {c c' : Aᵒᵖ} (f : c ⟶ c')
    (x : (c.unop ⟶ a) × (c.unop ⟶ b)) :
    (produitRep a b).map f x = (f.unop ≫ x.1, f.unop ≫ x.2) := rfl

/-- `A_{/X}` for a presheaf `X`: the category of pairs `(c, yoneda c → X)`. -/
abbrev Tranche {A : Type u} [Category.{u} A] (X : Aᵒᵖ ⥤ Type u) : Type u :=
  CostructuredArrow yoneda X

/-- The object `(c, (p, q))` of `A_{/a × b}` given by a span `a ← c → b`. -/
def span {A : Type u} [Category.{u} A] {a b c : A} (p : c ⟶ a) (q : c ⟶ b) :
    Tranche (produitRep a b) :=
  CostructuredArrow.mk (Y := c)
    { app := fun _ => TypeCat.ofHom fun f => (f ≫ p, f ≫ q)
      naturality := by
        intros; ext x
        exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _) }

/-- The element of `(a × b)(c)` that an object `(c, ξ)` of `A_{/a×b}` stands for
(Yoneda). -/
def elt {A : Type u} [Category.{u} A] {a b : A} (Y : Tranche (produitRep a b)) :
    (Y.left ⟶ a) × (Y.left ⟶ b) :=
  (show (produitRep a b).obj (Opposite.op Y.left) from Y.hom.app (Opposite.op Y.left) (𝟙 Y.left))

/-- `A` is *totally `W`-aspheric*: `W`-aspheric, and `a × b` is `W`-aspheric
in `Â` (i.e. `A_{/a×b}` is `W`-aspheric) for all `a, b`. -/
def TotalementAspherique (W : ClasseDeFoncteurs.{u}) (A : Type u) [Category.{u} A] : Prop :=
  Aspherique W A ∧ ∀ a b : A, Aspherique W (Tranche (produitRep a b))

/-- Condition (iii) of Proposition 4: `A` non-empty, and `a × b` `0`-connected
(`A_{/a×b}` non-empty and connected) for all `a, b`. -/
def ConditionIII (A : Type u) [Category.{u} A] : Prop :=
  Nonempty A ∧ ∀ a b : A, IsConnected (Tranche (produitRep a b))

/-- « il reste à voir que la dernière condition est exactement (iii) » :
totally `W₀`-aspheric is condition (iii) — including « (iii) implies that `A`
is `0`-connected ». -/
theorem totalementAspherique_W₀_iff (A : Type u) [Category.{u} A] :
    TotalementAspherique W₀ A ↔ ConditionIII A := by
  simp only [TotalementAspherique, ConditionIII, aspherique_W₀_iff]
  constructor
  · exact fun ⟨_, h⟩ => ⟨inferInstance, h⟩
  · rintro ⟨hA, h⟩
    refine ⟨zigzag_isConnected fun a b => ?_, h⟩
    obtain ⟨Y⟩ := (h a b).is_nonempty
    exact Zigzag.of_inv_hom (elt Y).1 (elt Y).2

/-! ### The minimal fundamental localiser -/

/-- The intersection of all fundamental localisers. -/
def Wmin : ClasseDeFoncteurs.{u} := fun _ _ _ _ F =>
  ∀ W : ClasseDeFoncteurs.{u}, LocalisateurFondamental W → W F

/-- The intersection of all fundamental localisers is one: the minimal
fundamental localiser exists. -/
theorem Wmin_localisateurFondamental : LocalisateurFondamental Wmin.{u} where
  id_mem A _ _ hW := hW.id_mem A
  comp_mem F G hF hG W hW := hW.comp_mem F G (hF W hW) (hG W hW)
  of_comp_left F G hF hFG W hW := hW.of_comp_left F G (hF W hW) (hFG W hW)
  of_comp_right F G hG hFG W hW := hW.of_comp_right F G (hG W hW) (hFG W hW)
  retract i r h hri W hW := hW.retract i r h (hri W hW)
  final A _ _ _ hW := hW.final A
  theoremeA v w h W hW := hW.theoremeA v w (fun c => h c W hW)

/-! ### The inclusion `W ⊆ W₀`, and what fails without it -/

/-- Inclusion of classes of functors. -/
def Inclus (W W' : ClasseDeFoncteurs.{u}) : Prop :=
  ∀ ⦃A B : Type u⦄ [Category.{u} A] [Category.{u} B] (F : A ⥤ B), W F → W' F

/-- `W_∞ ⊆ W`: the minimal localiser is contained in every fundamental
localiser. -/
theorem Wmin_inclus {W : ClasseDeFoncteurs.{u}} (hW : LocalisateurFondamental W) :
    Inclus Wmin W := fun _ _ _ _ _ hF => hF W hW

/-- Total asphericity is monotone in the localiser. -/
theorem totalementAspherique_mono {W W' : ClasseDeFoncteurs.{u}} (h : Inclus W W')
    {A : Type u} [Category.{u} A] (hA : TotalementAspherique W A) :
    TotalementAspherique W' A :=
  ⟨h _ hA.1, fun a b => h _ (hA.2 a b)⟩

/-- **Proposition 4, (i) ⇒ (ii)**, with `W_∞` the minimal fundamental
localiser. -/
theorem proposition4_i_ii {W : ClasseDeFoncteurs.{u}} (hW : LocalisateurFondamental W)
    {A : Type u} [Category.{u} A] (h : TotalementAspherique Wmin A) :
    TotalementAspherique W A :=
  totalementAspherique_mono (Wmin_inclus hW) h

/-- The argument of Proposition 4 for (ii) ⇒ (iii), with the inclusion
`W ⊆ W₀` it needs made a hypothesis. -/
theorem proposition4_ii_iii {W : ClasseDeFoncteurs.{u}} (hW : Inclus W W₀)
    (A : Type u) [Category.{u} A] (h : TotalementAspherique W A) : ConditionIII A :=
  (totalementAspherique_W₀_iff A).1 (totalementAspherique_mono hW h)

/-- The class of all functors (the trivial localiser). -/
def Wtrivial : ClasseDeFoncteurs.{u} := fun _ _ _ _ _ => True

theorem Wtrivial_localisateurFondamental : LocalisateurFondamental Wtrivial.{u} where
  id_mem _ _ := trivial
  comp_mem _ _ _ _ := trivial
  of_comp_left _ _ _ _ := trivial
  of_comp_right _ _ _ _ := trivial
  retract _ _ _ _ := trivial
  final _ _ _ := trivial
  theoremeA _ _ _ := trivial

/-- `W₋₁`: the functors `A → B` with `A` empty iff `B` empty. -/
def Wmoins1 : ClasseDeFoncteurs.{u} := fun A B _ _ _ => (Nonempty A ↔ Nonempty B)

theorem Wmoins1_localisateurFondamental : LocalisateurFondamental Wmoins1.{u} where
  id_mem _ _ := Iff.rfl
  comp_mem _ _ h₁ h₂ := h₁.trans h₂
  of_comp_left _ _ h₁ h₂ := h₁.symm.trans h₂
  of_comp_right _ _ h₁ h₂ := h₂.trans h₁.symm
  retract i r _ _ := ⟨fun ⟨b⟩ => ⟨r.obj b⟩, fun ⟨a⟩ => ⟨i.obj a⟩⟩
  final A _ _ := ⟨fun _ => ⟨⟨⟨⟩⟩⟩, fun _ => ⟨⊤_ A⟩⟩
  theoremeA := by
    intro A B C _ _ _ v w h
    refine ⟨fun ⟨a⟩ => ⟨v.obj a⟩, fun ⟨b⟩ => ?_⟩
    obtain ⟨α⟩ := (h (w.obj b)).2 ⟨CostructuredArrow.mk (𝟙 (w.obj b))⟩
    exact ⟨α.left⟩

/-- `Discrete (ULift Bool) → e` is in `W₋₁` and in the trivial localiser, but
not in `W₀`. -/
theorem star_deuxPoints_not_W₀ : ¬ W₀ (Functor.star.{u} (Discrete (ULift.{u} Bool))) := by
  rintro ⟨hinj, -⟩
  have := Quotient.exact (hinj (a₁ := Quotient.mk _ ⟨⟨true⟩⟩) (a₂ := Quotient.mk _ ⟨⟨false⟩⟩) rfl)
  simpa using eq_of_zigzag _ this

/-- **Finding: `W₀` is not the coarsest fundamental localiser.** `W₋₁` is a
fundamental localiser that is not contained in `W₀`. -/
theorem Wmoins1_not_inclus_W₀ : ¬ Inclus Wmoins1.{u} W₀.{u} := fun h =>
  star_deuxPoints_not_W₀ (h _ (show Nonempty _ ↔ Nonempty _ from
    ⟨fun _ => ⟨⟨⟨⟩⟩⟩, fun _ => ⟨⟨⟨true⟩⟩⟩⟩))

/-- … nor is the trivial one. -/
theorem Wtrivial_not_inclus_W₀ : ¬ Inclus Wtrivial.{u} W₀.{u} := fun h =>
  star_deuxPoints_not_W₀ (h _ trivial)

/-! ### A counterexample to (ii) ⇒ (iii) for `W = W₋₁` -/

/-- The group `ℤ/2`, written multiplicatively. -/
abbrev G2 := Multiplicative (ZMod 2)

/-- The one-object category `B(ℤ/2)`. -/
abbrev BG2 := SingleObj G2

/-- An arrow of `B(ℤ/2)`, as an element of the group. -/
abbrev toG {a b : BG2} (f : a ⟶ b) : G2 := f

/-- An element of the group, as an arrow of `B(ℤ/2)`. -/
abbrev fl (m : G2) : SingleObj.star G2 ⟶ SingleObj.star G2 := m

lemma elt_left_eq {Y Y' : Tranche (produitRep (SingleObj.star G2) (SingleObj.star G2))}
    (g : Y ⟶ Y') :
    elt Y = (g.left ≫ (elt Y').1, g.left ≫ (elt Y').2) := by
  have e1 := ConcreteCategory.congr_hom
    (NatTrans.congr_app (CostructuredArrow.w g) (Opposite.op Y.left)) (𝟙 Y.left)
  have nat := NatTrans.naturality_apply Y'.hom g.left.op (𝟙 Y'.left)
  unfold elt
  rw [← e1, NatTrans.comp_app_apply]
  simp only [yoneda_map_app, yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk, Category.id_comp, Category.comp_id] at nat ⊢
  exact nat

/-- The invariant `x₁⁻¹ x₂` of an element `(x₁, x₂)` of `(∗ × ∗)(∗) = G × G`. -/
def invariant (Y : Tranche (produitRep (SingleObj.star G2) (SingleObj.star G2))) : G2 :=
  (toG (elt Y).1)⁻¹ * toG (elt Y).2

lemma invariant_eq {Y Y' : Tranche (produitRep (SingleObj.star G2) (SingleObj.star G2))}
    (g : Y ⟶ Y') : invariant Y = invariant Y' := by
  unfold invariant
  rw [elt_left_eq g]
  show (toG (elt Y').1 * toG g.left)⁻¹ * (toG (elt Y').2 * toG g.left) = _
  rw [mul_comm (toG (elt Y').1), mul_comm (toG (elt Y').2), mul_inv_rev, mul_assoc,
    inv_mul_cancel_left]

lemma invariant_zigzag {Y Y' : Tranche (produitRep (SingleObj.star G2) (SingleObj.star G2))}
    (h : Zigzag Y Y') : invariant Y = invariant Y' := by
  induction h with
  | refl => rfl
  | tail _ hzag ih =>
    rcases hzag with ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
    · exact ih.trans (invariant_eq g)
    · exact ih.trans (invariant_eq g).symm

lemma invariant_span (p q : SingleObj.star G2 ⟶ SingleObj.star G2) :
    invariant (span p q) = (toG p)⁻¹ * toG q := by
  change (toG (𝟙 _ ≫ p))⁻¹ * toG (𝟙 _ ≫ q) = _
  rw [Category.id_comp, Category.id_comp]

/-- **Finding: Proposition 4, (ii) ⇒ (iii), fails for the fundamental localiser
`W₋₁`.** `B(ℤ/2)` is totally `W₋₁`-aspheric, but `∗ × ∗` is not
`0`-connected. -/
theorem contreExemple_proposition4 :
    TotalementAspherique Wmoins1.{0} BG2 ∧ ¬ ConditionIII BG2 := by
  refine ⟨⟨⟨fun _ => ⟨⟨⟨⟩⟩⟩, fun _ => ⟨SingleObj.star G2⟩⟩,
    fun a b => ⟨fun _ => ⟨⟨⟨⟩⟩⟩, fun _ => ⟨span (𝟙 a) (show a ⟶ b from (1 : G2))⟩⟩⟩, ?_⟩
  rintro ⟨-, h⟩
  have hc := h (SingleObj.star G2) (SingleObj.star G2)
  have := invariant_zigzag (isPreconnected_zigzag (span (fl 1) (fl 1))
    (span (fl 1) (fl (Multiplicative.ofAdd (1 : ZMod 2)))))
  rw [invariant_span, invariant_span] at this
  revert this
  decide

/-- **Finding: Proposition 4, (ii) ⇒ (i), fails for `W = W₋₁`.** `B(ℤ/2)` is
totally `W₋₁`-aspheric but not totally `W_∞`-aspheric: `W_∞ ⊆ W₀`, and
(iii) fails. -/
theorem contreExemple_proposition4_i_ii :
    TotalementAspherique Wmoins1.{0} BG2 ∧ ¬ TotalementAspherique Wmin.{0} BG2 :=
  ⟨contreExemple_proposition4.1, fun h => contreExemple_proposition4.2
    (proposition4_ii_iii (Wmin_inclus W₀_localisateurFondamental) _ h)⟩

end Grothendieck.Folder114
