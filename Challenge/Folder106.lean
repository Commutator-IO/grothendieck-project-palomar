module

public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

namespace Grothendieck.Folder106

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- A *catégorie à cofibrations* in the sense of Baues, as the reading's
conventions footnote recalls axioms C1–C3, on a category with an initial
object `∅`. -/
class CategorieACofibrations (W cof : MorphismProperty C) : Prop where
  /-- C1: isomorphisms are weak equivalences. -/
  iso_W : ∀ {x y : C} (e : x ≅ y), W e.hom
  /-- C1: isomorphisms are cofibrations. -/
  iso_cof : ∀ {x y : C} (e : x ≅ y), cof e.hom
  /-- C1: composites of cofibrations are cofibrations. -/
  cof_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), cof f → cof g → cof (f ≫ g)
  /-- C1, two-out-of-three: the composite of two weak equivalences is one. -/
  W_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W f → W g → W (f ≫ g)
  /-- C1, two-out-of-three: if `f` and `f ≫ g` are weak equivalences, so is `g`. -/
  W_of_comp_left : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W f → W (f ≫ g) → W g
  /-- C1, two-out-of-three: if `g` and `f ≫ g` are weak equivalences, so is `f`. -/
  W_of_comp_right : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W g → W (f ≫ g) → W f
  /-- C2: the pushout along a cofibration exists. -/
  hasPushout : ∀ {b a y : C} (c : b ⟶ a) (u : b ⟶ y), cof c → HasPushout c u
  /-- C2: in a pushout square `c ≫ u' = u ≫ c'` with `c : b → a` a cofibration,
  `c' : y → a ∨_b y` is a cofibration. -/
  pushout_cof : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → cof c'
  /-- C2: … and a weak equivalence if `c` is one. -/
  pushout_W_of_W : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → W c → W c'
  /-- C2: `u' : a → a ∨_b y` is a weak equivalence if `u` is one. -/
  pushout_W_of_W' : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → W u → W u'
  /-- C3: every arrow factors as a cofibration followed by a weak equivalence. -/
  factorisation : ∀ {x y : C} (f : x ⟶ y),
    ∃ (z : C) (i : x ⟶ z) (p : z ⟶ y), cof i ∧ W p ∧ i ≫ p = f

/-- An object `x` is *cofibrant* when `∅ → x` is a cofibration. -/
def Cofibrant (cof : MorphismProperty C) (x : C) : Prop := cof (initial.to x)

variable {W cof : MorphismProperty C} [CategorieACofibrations W cof]

namespace CategorieACofibrations

omit [HasInitial C] in
include cof in
lemma W_id (x : C) : W (𝟙 x) := iso_W (cof := cof) (Iso.refl x)

omit [HasInitial C] in
open Localization.Construction in
@[reassoc (attr := simp)]
lemma wInv_hom {x y : C} (w : x ⟶ y) (hw : W w) : wInv w hw ≫ W.Q.map w = 𝟙 _ :=
  (wIso w hw).inv_hom_id

variable (W cof) in
/-- **Page 11, an object of `Ch'₀(x, y)`**: a diagram `x → ỹ ← y`, the first
arrow a cofibration, the second a weak equivalence. -/
structure Span (x y : C) where
  /-- the middle object `ỹ` -/
  pt : C
  /-- the forward arrow `x → ỹ` -/
  f : x ⟶ pt
  /-- the backward arrow `y → ỹ` -/
  i : y ⟶ pt
  hf : cof f
  hi : W i

namespace Span

variable {x y z w : C}

/-- An arrow `(f, i) → (f', i')` of `Ch'₀(x, y)`: `u : ỹ → ỹ'` with `u f = f'`
and `u i = i'`. Two diagrams lie in the same connected component of `Ch'₀(x, y)`
when they are related by the equivalence relation this generates. -/
def Arrow (s t : Span W cof x y) : Prop := ∃ u : s.pt ⟶ t.pt, s.f ≫ u = t.f ∧ s.i ≫ u = t.i

/-- The fraction `[i]⁻¹[f] : x → y` in `W⁻¹𝒞` of a diagram `(f, i)`. -/
noncomputable def frac (s : Span W cof x y) : W.Q.obj x ⟶ W.Q.obj y :=
  W.Q.map s.f ≫ Localization.Construction.wInv s.i s.hi

omit [HasInitial C] [CategorieACofibrations W cof] in
lemma frac_eq_of_arrow {s t : Span W cof x y} (h : Arrow s t) : s.frac = t.frac := by
  obtain ⟨u, h1, h2⟩ := h
  unfold frac
  have := W.Q_inverts t.i t.hi
  rw [← cancel_mono (W.Q.map t.i)]
  simp only [Category.assoc, wInv_hom, Category.comp_id]
  rw [← h2, W.Q.map_comp, wInv_hom_assoc, ← W.Q.map_comp, h1]

end Span

open Span

variable (W cof) in
/-- `π₀ Ch'₀(x, y)`, the set of connected components of `Ch'₀(x, y)`. -/
abbrev Pi0 (x y : C) : Type _ := Quot (Span.Arrow (W := W) (cof := cof) (x := x) (y := y))

/-- The map `π₀ Ch'₀(x, y) → W⁻¹𝒞(x, y)`, `(f, i) ↦ [i]⁻¹[f]`: the functor
`q'` of page 15 on arrows. -/
noncomputable def qbar {x y : C} : Pi0 W cof x y → (W.Q.obj x ⟶ W.Q.obj y) :=
  Quot.lift Span.frac (fun _ _ h => frac_eq_of_arrow h)

/-- The diagram `(1_x, i) : x → x ← y` of a section `i` of `f : x → y` in `W`. -/
@[reducible] def sectionSpan {x y : C} (f : x ⟶ y) (hf : W f) (i : y ⟶ x) (hi : i ≫ f = 𝟙 y) :
    Span W cof x y :=
  ⟨x, 𝟙 x, i, iso_cof (W := W) (cof := cof) (Iso.refl x),
    W_of_comp_right (cof := cof) i f hf (hi ▸ W_id (cof := cof) y)⟩

variable (W cof) in
/-- **The criterion `(⋆⋆)` of page 15.** For `f : x → y` in `W` and two sections
`i, i'` of `f`, the diagrams `(1_x, i)` and `(1_x, i')` lie in the same connected
component of `Ch'₀(x, y)`. -/
def Critere : Prop :=
  ∀ ⦃x y : C⦄ (f : x ⟶ y) (hf : W f) (i i' : y ⟶ x) (hi : i ≫ f = 𝟙 y) (hi' : i' ≫ f = 𝟙 y),
    Relation.EqvGen Span.Arrow (sectionSpan (cof := cof) f hf i hi) (sectionSpan f hf i' hi')

/-- **The final statement of page 15, as the finding states it**: when every
object is cofibrant, `q'` is faithful if and only if `(⋆⋆)` holds. (Both sides
hold: `fidele`, `critere`.) -/
theorem fidele_iff_critere (hcof : ∀ x : C, Cofibrant cof x) :
    (∀ x y : C, Function.Injective (qbar (W := W) (cof := cof) (x := x) (y := y))) ↔
      Critere W cof := by
  sorry

end CategorieACofibrations

end Grothendieck.Folder106
