module

public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section


/-!
# Folder 106: cofibration categories and Brown's factorisation lemma

The modernised reading `transcripts/106/106.modern.tex` works in a category `𝒞`
with an initial object `∅`, weak equivalences `W` and cofibrations `cof`
satisfying Baues's axioms C1–C3, which its conventions footnote recalls (from
memory) as follows:

> C1, les isomorphismes sont dans `W` et dans `cof`, les composés de
> cofibrations sont des cofibrations, et `W` satisfait au deux-sur-trois ;
> C2, pour une cofibration `c : b → a` et une flèche `u : b → y`, la somme
> amalgamée `a ∨_b y` existe, la flèche `y → a ∨_b y` est une cofibration, et
> une équivalence faible si `c` en est une, et la flèche `a → a ∨_b y` est une
> équivalence faible si `u` en est une ; C3, toute flèche se factorise en une
> cofibration suivie d'une équivalence faible.

These are the fields of `CategorieACofibrations` below, verbatim. C2 is stated
for every pushout square (`IsPushout`) rather than for a chosen pushout; since
C1 puts the isomorphisms in `W` and `cof`, and both are closed under
composition, the two formulations are equivalent.

This file formalises, first, what issue #26 names for the folder — the
cofibration-category axioms and Brown's factorisation — namely three statements
of the reading:

* **Page 1, the « weak lifting lemma »** (`relevementFaible`), in the form the
  reading derives from C1–C3: given `f : x → y`, `α_x : x̃ → x`, `α_y : ỹ → y`
  in `W` with `x̃, ỹ` cofibrant, there are `i : ỹ → ỹ'` in `cof ∩ W`,
  `α'_y : ỹ' → y` in `W` with `α_y = α'_y i`, and `f̃ : x̃ → ỹ'` with
  `α'_y f̃ = f α_x`. The proof is the reading's: factor `(α_y, f α_x)` out of
  `ỹ ∨ x̃`. The formalisation adds that `ỹ'` is cofibrant, which the reading
  uses (it puts `[i]⁻¹[f̃]` in `W_cof⁻¹𝒞_cof`) without saying it.
* **Page 9, Brown's factorisation** (`factorisationDeBrown`): `x, y` cofibrant,
  `f : x → y` in `W`; factoring `(f, 1_y) : x ⊔ y → y` gives `α i = f`,
  `α g = 1_y`, `i, g ∈ cof ∩ W`, `α ∈ W`.
* **Page 11, the doubt lifted** (`inverse_W_of_inverse_W₀`,
  `localisation_W₀_iso_localisation_W`): when every object is cofibrant, a
  functor that inverts `W₀ = W ∩ cof` inverts `W`, and so
  `W₀⁻¹𝒞 → W⁻¹𝒞` is an isomorphism of categories — stated here as a pair of
  mutually inverse functors (equalities of functors, not natural isomorphisms)
  compatible with the two localisation functors.

What the formalisation finds. All three hold as the reading states them, with
no hypothesis added. Two hypotheses are more than the proofs use, and the
general forms are proved alongside:
* in the weak lifting lemma, `α_x ∈ W` is not used, and `ỹ` need not be
  cofibrant for `i` to be a cofibration — only `x̃` must be (as the reading
  itself says: « parce que `x̃` est cofibrant »); `ỹ` cofibrant is used only to
  make `ỹ'` cofibrant;
* in Brown's factorisation, `f ∈ W` is used only for `i ∈ W`; for an arbitrary
  `f` between cofibrant objects one still gets `i ∈ cof`, `g ∈ cof ∩ W`,
  `α ∈ W` (`factorisationDeBrown_general`). For these three statements, of C2
  only the existence of pushouts along a cofibration and the stability of
  cofibrations under cobase change are used.

Second, the finding `106-section-criterion-span-faithfulness`, pages 11 to 15:
every object cofibrant, `Ch'₀(x, y)` the category of diagrams
`x → ỹ ← y`, the first arrow a cofibration, the second in `W` (`Span`, with
arrows `Span.Arrow`), `𝒞̃'` the category of their connected components
(`Rect`, composition by pushout along the cofibration, page 5's formula), and
`q' : 𝒞̃' → W⁻¹𝒞`, `(f, i) ↦ [i]⁻¹[f]` (`qFunctor`, on arrows `qbar`). Proved:
* **necessity of `(⋆⋆)`** (`critere_of_fidele`): if `q'` is faithful, then for
  `f : x → y` in `W` and two sections `i, i'`, the diagrams `(1_x, i)` and
  `(1_x, i')` lie in the same component — the reading's argument;
* **`q'` is faithful, unconditionally** (`fidele`), and therefore `(⋆⋆)` always
  holds (`critere`); the finding's « iff » (`fidele_iff_critere`) holds with
  both sides true;
* **`q'` is full** (`plein`) and **an isomorphism of categories**
  (`qFunctor_iso`, inverse functor `phiBar`, equalities of functors).
The proof is not the one the page sketches: it never compares two sections.
It maps `𝒞` to `𝒞̃'` by `F ↦` the diagram of a Brown factorisation of `F`
(`phi`), shows that any diagram `(f, i)` with a retraction `ψ`, `ψ i = 1`,
`ψ f = F`, lies in the component of that diagram (`arrow_brown`: push out the
factorisation's cofibration `x ⊔ z → z̄` along `(f, i)` and factor the map to
`z` by C3), deduces functoriality and that `phi` inverts `W` (through page 11's
`inverse_W_of_inverse_W₀`), and checks `(f, i) = φ(i)⁻¹ ∘ φ(f)`. The
composition of `𝒞̃'` uses the clause of C2 that the pushout of a weak
equivalence along a cofibration is a weak equivalence; the other weak-equivalence
clause of C2 (`pushout_W_of_W`) is used nowhere in the file. The clause of C1
that isomorphisms are cofibrations, unused by the first three statements, is
used here: the unit `(1_x, 1_x)` and the diagrams `(1_x, i)` of `(⋆⋆)` need
`1_x ∈ cof`.

Not formalised: the Proposition of page 5 (`Ψ` is an equivalence iff `(⋆)`),
the reduction to `𝒞_cof`, page 5's first categories `Ch₀`, `𝒞̃` (backward arrow
in `cof ∩ W`) and the fullness of their `q` on page 9, and page 13's
construction of the image of an arrow with a separately chosen section.

What this certifies is that the reading holds together, not that it is what the
page says (issue #26).
-/

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

include W in
/-- Composing a cofibration `∅ → x` with a cofibration `x → z` shows `z`
cofibrant. -/
lemma cofibrant_of_cof {x z : C} (hx : Cofibrant cof x) (i : x ⟶ z) (hi : cof i) :
    Cofibrant cof z :=
  (Subsingleton.elim (initial.to x ≫ i) (initial.to z) ▸ cof_comp (W := W) _ _ hx hi :
    cof (initial.to z))

/-- Cofibrant replacement (page 1): C3 applied to `∅ → x` gives `α_x : x̃ → x`
in `W` with `x̃` cofibrant. -/
theorem remplacementCofibrant (x : C) :
    ∃ (x' : C) (α : x' ⟶ x), Cofibrant cof x' ∧ W α := by
  obtain ⟨z, i, p, hi, hp, -⟩ := factorisation (W := W) (cof := cof) (initial.to x)
  exact ⟨z, p, (Subsingleton.elim i (initial.to z) ▸ hi : cof (initial.to z)), hp⟩

/-- The common core of pages 1 and 9. Given `p : a → y` and `q : b → y` with
`b` cofibrant, the sum `a ⊔ b` (the pushout of `∅ → b` along `∅ → a`) exists,
and factoring `(p, q) : a ⊔ b → y` by C3 gives `ja : a → z`, `jb : b → z`,
`w : z → y` with `w ∈ W`, `ja ≫ w = p`, `jb ≫ w = q`; `ja` is a cofibration
because `b` is cofibrant, and `jb` is one as soon as `a` is. -/
theorem factorisation_somme {a b y : C} (hb : Cofibrant cof b) (p : a ⟶ y) (q : b ⟶ y) :
    ∃ (z : C) (ja : a ⟶ z) (jb : b ⟶ z) (w : z ⟶ y),
      cof ja ∧ W w ∧ ja ≫ w = p ∧ jb ≫ w = q ∧ (Cofibrant cof a → cof jb) := by
  have := hasPushout (W := W) (initial.to b) (initial.to a) hb
  have hP := IsPushout.of_hasPushout (initial.to b) (initial.to a)
  -- `pushout.inl : b → a ⊔ b`, `pushout.inr : a → a ⊔ b`
  obtain ⟨z, c, w, hc, hw, hcw⟩ := factorisation (W := W) (cof := cof)
    (hP.desc q p (Subsingleton.elim _ _))
  refine ⟨z, pushout.inr _ _ ≫ c, pushout.inl _ _ ≫ c, w,
    cof_comp (W := W) _ _ (pushout_cof (W := W) hP hb) hc, hw, ?_, ?_, ?_⟩
  · rw [Category.assoc, hcw, hP.inr_desc]
  · rw [Category.assoc, hcw, hP.inl_desc]
  · exact fun ha => cof_comp (W := W) _ _ (pushout_cof (W := W) hP.flip ha) hc

/-- **Page 1, the weak lifting lemma, general form.** Given `f : x → y`,
`α_x : x̃ → x`, `α_y : ỹ → y ∈ W` with `x̃` cofibrant, there are
`i : ỹ → ỹ'` in `cof ∩ W`, `α'_y : ỹ' → y` in `W` with `α_y = α'_y i`, and
`f̃ : x̃ → ỹ'` with `α'_y f̃ = f α_x`; and `ỹ'` is cofibrant if `ỹ` is.
Neither `α_x ∈ W` nor `ỹ` cofibrant is needed for the lifting itself. -/
theorem relevementFaible_general {x y x' y' : C} (f : x ⟶ y) (αx : x' ⟶ x) (αy : y' ⟶ y)
    (hαy : W αy) (hx' : Cofibrant cof x') :
    ∃ (y'' : C) (i : y' ⟶ y'') (α' : y'' ⟶ y) (f' : x' ⟶ y''),
      cof i ∧ W i ∧ W α' ∧ i ≫ α' = αy ∧ f' ≫ α' = αx ≫ f ∧
      (Cofibrant cof y' → Cofibrant cof y'') := by
  obtain ⟨z, ja, jb, w, hja, hw, h1, h2, -⟩ := factorisation_somme (W := W) hx' αy (αx ≫ f)
  refine ⟨z, ja, w, jb, hja, W_of_comp_right (cof := cof) _ _ hw (h1 ▸ hαy), hw, h1, h2,
    fun hy' => cofibrant_of_cof (W := W) hy' ja hja⟩

/-- **Page 1, the weak lifting lemma, as the reading states it**, for cofibrant
replacements `α_x : x̃ → x`, `α_y : ỹ → y` (cofibrant sources, arrows in `W`):
there are `i : ỹ → ỹ'` in `cof ∩ W`, `α'_y : ỹ' → y` in `W` with
`α_y = α'_y i`, and `f̃ : x̃ → ỹ'` with `α'_y f̃ = f α_x`; moreover `ỹ'` is
cofibrant. -/
theorem relevementFaible {x y x' y' : C} (f : x ⟶ y) (αx : x' ⟶ x) (αy : y' ⟶ y)
    (hx' : Cofibrant cof x') (_hαx : W αx) (hy' : Cofibrant cof y') (hαy : W αy) :
    ∃ (y'' : C) (i : y' ⟶ y'') (α' : y'' ⟶ y) (f' : x' ⟶ y''),
      cof i ∧ W i ∧ W α' ∧ i ≫ α' = αy ∧ f' ≫ α' = αx ≫ f ∧ Cofibrant cof y'' := by
  obtain ⟨y'', i, α', f', h1, h2, h3, h4, h5, h6⟩ :=
    relevementFaible_general (W := W) f αx αy hαy hx'
  exact ⟨y'', i, α', f', h1, h2, h3, h4, h5, h6 hy'⟩

/-- **Brown's factorisation, general form.** For any `f : x → y` between
cofibrant objects, factoring `(f, 1_y) : x ⊔ y → y` gives `x̄`, `i : x → x̄`
cofibration, `g : y → x̄` in `cof ∩ W`, `α : x̄ → y` in `W`, with `α i = f` and
`α g = 1_y`. -/
theorem factorisationDeBrown_general {x y : C} (hx : Cofibrant cof x) (hy : Cofibrant cof y)
    (f : x ⟶ y) :
    ∃ (x' : C) (i : x ⟶ x') (g : y ⟶ x') (α : x' ⟶ y),
      cof i ∧ cof g ∧ W g ∧ W α ∧ i ≫ α = f ∧ g ≫ α = 𝟙 y := by
  obtain ⟨z, ja, jb, w, hja, hw, h1, h2, h3⟩ := factorisation_somme (W := W) hy f (𝟙 y)
  refine ⟨z, ja, jb, w, hja, h3 hx, ?_, hw, h1, h2⟩
  exact W_of_comp_right (cof := cof) _ _ hw (h2 ▸ W_id (cof := cof) y)

/-- **Page 9, Brown's factorisation, as the reading states it.** Let `x, y` be
cofibrant and `f : x → y` in `W`. Factoring `(f, 1_y) : x ⊔ y → y` as a
cofibration followed by `α : x̄ → y` in `W`, and writing `i`, `g` for the
composites of `x → x ⊔ y`, `y → x ⊔ y` with `x ⊔ y → x̄`, one has `α i = f`,
`α g = 1_y`, and `i, g ∈ cof ∩ W`. -/
theorem factorisationDeBrown {x y : C} (hx : Cofibrant cof x) (hy : Cofibrant cof y)
    (f : x ⟶ y) (hf : W f) :
    ∃ (x' : C) (i : x ⟶ x') (g : y ⟶ x') (α : x' ⟶ y),
      cof i ∧ W i ∧ cof g ∧ W g ∧ W α ∧ i ≫ α = f ∧ g ≫ α = 𝟙 y := by
  obtain ⟨x', i, g, α, hi, hg, hgW, hα, h1, h2⟩ := factorisationDeBrown_general (W := W) hx hy f
  exact ⟨x', i, g, α, hi, W_of_comp_right (cof := cof) _ _ hα (h1 ▸ hf), hg, hgW, hα, h1, h2⟩

/-- **Page 11, the doubt lifted.** When every object is cofibrant, a functor
inverting the trivial cofibrations `W₀ = W ∩ cof` inverts every weak
equivalence: write `f = α i` with `α g = 1_y` and `i, g ∈ W₀` (page 9); then
`[α] = [g]⁻¹` and `[f] = [α][i]` are invertible. -/
theorem inverse_W_of_inverse_W₀ (hcof : ∀ x : C, Cofibrant cof x) {D : Type*} [Category D]
    (F : C ⥤ D) (hF : (W ⊓ cof).IsInvertedBy F) : W.IsInvertedBy F := by
  intro x y f hf
  obtain ⟨x', i, g, α, hi, hiW, hg, hgW, -, h1, h2⟩ :=
    factorisationDeBrown (W := W) (hcof x) (hcof y) f hf
  have := hF i ⟨hiW, hi⟩
  have := hF g ⟨hgW, hg⟩
  have hα : F.map α = inv (F.map g) := by
    rw [← cancel_epi (F.map g), IsIso.hom_inv_id, ← F.map_comp, h2, F.map_id]
  have : IsIso (F.map α) := by rw [hα]; infer_instance
  rw [← h1, F.map_comp]
  infer_instance

/-- **Page 11: `W₀⁻¹𝒞 → W⁻¹𝒞` is an isomorphism of categories** when every
object is cofibrant, `W₀ = W ∩ cof`. Stated as a pair of functors
`F : W₀⁻¹𝒞 → W⁻¹𝒞`, `G : W⁻¹𝒞 → W₀⁻¹𝒞`, compatible with the localisation
functors, with `F ⋙ G` and `G ⋙ F` *equal* to the identities. -/
theorem localisation_W₀_iso_localisation_W (hcof : ∀ x : C, Cofibrant cof x) :
    ∃ (F : (W ⊓ cof).Localization ⥤ W.Localization)
      (G : W.Localization ⥤ (W ⊓ cof).Localization),
      (W ⊓ cof).Q ⋙ F = W.Q ∧ W.Q ⋙ G = (W ⊓ cof).Q ∧
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ := by
  have hF : (W ⊓ cof).IsInvertedBy W.Q := fun _ _ f hf => W.Q_inverts f hf.1
  have hG : W.IsInvertedBy (W ⊓ cof).Q :=
    inverse_W_of_inverse_W₀ (W := W) hcof _ (W ⊓ cof).Q_inverts
  refine ⟨Localization.Construction.lift _ hF, Localization.Construction.lift _ hG,
    Localization.Construction.fac _ hF, Localization.Construction.fac _ hG, ?_, ?_⟩
  · apply Localization.Construction.uniq
    rw [← Functor.assoc, Localization.Construction.fac, Localization.Construction.fac]
    rfl
  · apply Localization.Construction.uniq
    rw [← Functor.assoc, Localization.Construction.fac, Localization.Construction.fac]
    rfl

/-! ### Pages 11 to 15: the rectified spans `Ch'₀(x, y)` and the criterion `(⋆⋆)` -/

omit [HasInitial C] in
open Localization.Construction in
@[reassoc (attr := simp)]
lemma wInv_hom {x y : C} (w : x ⟶ y) (hw : W w) : wInv w hw ≫ W.Q.map w = 𝟙 _ :=
  (wIso w hw).inv_hom_id

omit [HasInitial C] in
open Localization.Construction in
@[reassoc (attr := simp)]
lemma hom_wInv {x y : C} (w : x ⟶ y) (hw : W w) : W.Q.map w ≫ wInv w hw = 𝟙 _ :=
  (wIso w hw).hom_inv_id

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

omit [HasInitial C] [CategorieACofibrations W cof] in
/-- If `ψ : ỹ → y` retracts `i` (`ψ i = 1_y`) and `ψ f = F`, then `[i]⁻¹[f] = [F]`. -/
lemma frac_of_retraction (s : Span W cof x z) (ψ : s.pt ⟶ z) (F : x ⟶ z)
    (hz : s.i ≫ ψ = 𝟙 z) (hx : s.f ≫ ψ = F) : s.frac = W.Q.map F := by
  have := W.Q_inverts s.i s.hi
  have : Localization.Construction.wInv s.i s.hi = W.Q.map ψ := by
    rw [← cancel_epi (W.Q.map s.i), hom_wInv, ← W.Q.map_comp, hz, W.Q.map_id]
  rw [frac, this, ← W.Q.map_comp, hx]

/-- The composite of page 5, with page 11's conditions: for `(f, i) : x → ỹ ← y`
and `(g, j) : y → z̃ ← z`, push out `ỹ ← y → z̃` along the cofibration `g`; the
composite is `(g' f, k j)`. That `k : z̃ → ỹ ∨_y z̃` is a weak equivalence is
the clause of C2 on the pushout of a weak equivalence along a cofibration. -/
@[reducible] noncomputable def comp (s : Span W cof x y) (t : Span W cof y z) : Span W cof x z :=
  have := hasPushout (W := W) (cof := cof) t.f s.i t.hf
  { pt := pushout t.f s.i
    f := s.f ≫ pushout.inr t.f s.i
    i := t.i ≫ pushout.inl t.f s.i
    hf := cof_comp (W := W) _ _ s.hf
      (pushout_cof (W := W) (IsPushout.of_hasPushout t.f s.i) t.hf)
    hi := W_comp (cof := cof) _ _ t.hi
      (pushout_W_of_W' (IsPushout.of_hasPushout t.f s.i) t.hf s.hi) }

omit [HasInitial C] in
lemma arrow_comp_left {s s' : Span W cof x y} (t : Span W cof y z) (h : Arrow s s') :
    Arrow (s.comp t) (s'.comp t) := by
  obtain ⟨u, h1, h2⟩ := h
  have := hasPushout (W := W) (cof := cof) t.f s.i t.hf
  have := hasPushout (W := W) (cof := cof) t.f s'.i t.hf
  refine ⟨pushout.desc (pushout.inl _ _) (u ≫ pushout.inr _ _) ?_, ?_, ?_⟩
  · rw [← Category.assoc, h2]; exact pushout.condition
  · show (s.f ≫ pushout.inr _ _) ≫ _ = s'.f ≫ pushout.inr _ _
    rw [Category.assoc, pushout.inr_desc, ← Category.assoc, h1]
  · show (t.i ≫ pushout.inl _ _) ≫ _ = t.i ≫ pushout.inl _ _
    rw [Category.assoc, pushout.inl_desc]

omit [HasInitial C] in
lemma arrow_comp_right (s : Span W cof x y) {t t' : Span W cof y z} (h : Arrow t t') :
    Arrow (s.comp t) (s.comp t') := by
  obtain ⟨v, h1, h2⟩ := h
  have := hasPushout (W := W) (cof := cof) t.f s.i t.hf
  have := hasPushout (W := W) (cof := cof) t'.f s.i t'.hf
  refine ⟨pushout.desc (v ≫ pushout.inl _ _) (pushout.inr _ _) ?_, ?_, ?_⟩
  · rw [← Category.assoc, h1]; exact pushout.condition
  · show (s.f ≫ pushout.inr _ _) ≫ _ = s.f ≫ pushout.inr _ _
    rw [Category.assoc, pushout.inr_desc]
  · show (t.i ≫ pushout.inl _ _) ≫ _ = t'.i ≫ pushout.inl _ _
    rw [Category.assoc, pushout.inl_desc, ← Category.assoc, h2]

/-- The unit `1_x = (1_x, 1_x)`. -/
@[reducible] def idSpan (x : C) : Span W cof x x :=
  ⟨x, 𝟙 x, 𝟙 x, iso_cof (W := W) (cof := cof) (Iso.refl x), W_id (cof := cof) x⟩

omit [HasInitial C] in
lemma arrow_id_comp (t : Span W cof x y) : Arrow t ((idSpan x).comp t) := by
  have := hasPushout (W := W) (cof := cof) t.f (𝟙 x) t.hf
  exact ⟨pushout.inl _ _, pushout.condition, rfl⟩

omit [HasInitial C] in
lemma arrow_comp_id (s : Span W cof x y) : Arrow s (s.comp (idSpan y)) := by
  have := hasPushout (W := W) (cof := cof) (𝟙 y) s.i (iso_cof (W := W) (cof := cof) (Iso.refl y))
  exact ⟨pushout.inr _ _, rfl, pushout.condition.symm⟩

omit [HasInitial C] in
lemma arrow_assoc (s : Span W cof x y) (t : Span W cof y z) (r : Span W cof z w) :
    Arrow ((s.comp t).comp r) (s.comp (t.comp r)) := by
  have := hasPushout (W := W) (cof := cof) t.f s.i t.hf
  have := hasPushout (W := W) (cof := cof) r.f (s.comp t).i r.hf
  have := hasPushout (W := W) (cof := cof) r.f t.i r.hf
  have := hasPushout (W := W) (cof := cof) (t.comp r).f s.i (t.comp r).hf
  have hA : t.f ≫ (pushout.inr r.f t.i ≫ pushout.inl (t.comp r).f s.i) =
      s.i ≫ pushout.inr (t.comp r).f s.i := by
    rw [← Category.assoc]; exact pushout.condition
  have hB : r.f ≫ (pushout.inl r.f t.i ≫ pushout.inl (t.comp r).f s.i) =
      (s.comp t).i ≫ pushout.desc _ _ hA := by
    show _ = (t.i ≫ pushout.inl t.f s.i) ≫ _
    rw [Category.assoc, pushout.inl_desc, ← Category.assoc, pushout.condition,
      Category.assoc]
  refine ⟨pushout.desc _ (pushout.desc _ _ hA) hB, ?_, ?_⟩
  · show ((s.f ≫ pushout.inr _ _) ≫ pushout.inr _ _) ≫ _ = s.f ≫ pushout.inr _ _
    simp only [Category.assoc, pushout.inr_desc]
  · show (r.i ≫ pushout.inl _ _) ≫ _ = (r.i ≫ pushout.inl _ _) ≫ pushout.inl _ _
    simp only [Category.assoc, pushout.inl_desc]

/-- The diagram `(g, 1) : x → x' ← x'` of a cofibration `g`. -/
@[reducible] def cofSpan {x y : C} (g : x ⟶ y) (hg : cof g) : Span W cof x y :=
  ⟨y, g, 𝟙 y, hg, W_id (cof := cof) y⟩

/-- The diagram `(1, w) : ỹ → ỹ ← y` of a weak equivalence `w : y → ỹ`, an arrow
`ỹ → y`. -/
@[reducible] def backSpan {y y' : C} (w : y ⟶ y') (hw : W w) : Span W cof y' y :=
  ⟨y', 𝟙 y', w, iso_cof (W := W) (cof := cof) (Iso.refl y'), hw⟩

omit [HasInitial C] in
/-- `(f, i) = (1, i) ∘ (f, 1)`, as page 15 writes it. -/
lemma arrow_decomp (s : Span W cof x y) :
    Arrow s ((cofSpan (W := W) s.f s.hf).comp (backSpan (cof := cof) s.i s.hi)) := by
  have := hasPushout (W := W) (cof := cof) (𝟙 s.pt) (𝟙 s.pt) (iso_cof (W := W) (cof := cof) (Iso.refl s.pt))
  have hlr : pushout.inl (𝟙 s.pt) (𝟙 s.pt) = pushout.inr _ _ := by
    simpa using (pushout.condition (f := 𝟙 s.pt) (g := 𝟙 s.pt))
  refine ⟨pushout.inr _ _, rfl, ?_⟩
  show _ = s.i ≫ pushout.inl _ _
  rw [hlr]

omit [HasInitial C] in
/-- For `g ∈ cof ∩ W`, `(1, g) ∘ (g, 1)` is in the component of the unit. -/
lemma arrow_cof_back {x y : C} (g : x ⟶ y) (hg : cof g) (hgW : W g) :
    Arrow (idSpan x) ((cofSpan (W := W) g hg).comp (backSpan (cof := cof) g hgW)) := by
  have := hasPushout (W := W) (cof := cof) (𝟙 y) (𝟙 y) (iso_cof (W := W) (cof := cof) (Iso.refl y))
  have hlr : pushout.inl (𝟙 y) (𝟙 y) = pushout.inr _ _ := by
    simpa using (pushout.condition (f := 𝟙 y) (g := 𝟙 y))
  refine ⟨g ≫ pushout.inl _ _, ?_, ?_⟩
  · show 𝟙 x ≫ g ≫ _ = g ≫ pushout.inr _ _
    rw [Category.id_comp, hlr]
  · show 𝟙 x ≫ g ≫ _ = g ≫ pushout.inl _ _
    rw [Category.id_comp]

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

omit [HasInitial C] in
/-- **Page 15, the necessity of `(⋆⋆)`.** If `q'` is faithful, `(⋆⋆)` holds:
`f i = 1_y` gives `q'(1_x, i) = [i]⁻¹ = [f] = q'(1_x, i')`. -/
theorem critere_of_fidele
    (h : ∀ x y : C, Function.Injective (qbar (W := W) (cof := cof) (x := x) (y := y))) :
    Critere W cof := by
  intro x y f hf i i' hi hi'
  have key : ∀ (j : y ⟶ x) (hj : j ≫ f = 𝟙 y),
      (sectionSpan (cof := cof) f hf j hj).frac = W.Q.map f := fun j hj =>
    frac_of_retraction _ f f hj (Category.id_comp f)
  exact Quot.eqvGen_exact (h x y (show frac _ = frac _ by rw [key, key]))

/-- The category `𝒞̃'` of page 11: the objects of `𝒞`, and `π₀ Ch'₀(x, y)` as
arrows `x → y`. -/
structure Rect (W cof : MorphismProperty C) where
  /-- the underlying object of `𝒞` -/
  as : C

noncomputable instance : Category (Rect W cof) where
  Hom X Y := Pi0 W cof X.as Y.as
  id X := Quot.mk _ (idSpan X.as)
  comp φ ψ := Quot.lift₂ (fun s t => Quot.mk _ (s.comp t))
    (fun s _ _ h => Quot.sound (arrow_comp_right s h))
    (fun _ _ t h => Quot.sound (arrow_comp_left t h)) φ ψ
  id_comp := by
    intro X Y φ
    induction φ using Quot.ind with
    | mk t => exact (Quot.sound (arrow_id_comp t)).symm
  comp_id := by
    intro X Y φ
    induction φ using Quot.ind with
    | mk s => exact (Quot.sound (arrow_comp_id s)).symm
  assoc := by
    intro X Y Z T φ ψ χ
    induction φ using Quot.ind with
    | mk s =>
    induction ψ using Quot.ind with
    | mk t =>
    induction χ using Quot.ind with
    | mk r => exact Quot.sound (arrow_assoc s t r)

/-- The data of a Brown factorisation of `F : x → z` (page 9): the sum `x ⊔ z`,
a cofibration `c : x ⊔ z → z̄` and `α : z̄ → z` in `W` with `α c = (F, 1_z)`. -/
structure Brown {x z : C} (F : x ⟶ z) where
  /-- the sum `x ⊔ z` -/
  S : C
  ιz : z ⟶ S
  ιx : x ⟶ S
  hS : IsPushout (initial.to z) (initial.to x) ιz ιx
  /-- the middle object `z̄` -/
  pt : C
  c : S ⟶ pt
  α : pt ⟶ z
  hc : cof c
  hα : W α
  hιx : cof ιx
  hz : ιz ≫ c ≫ α = 𝟙 z
  hx : ιx ≫ c ≫ α = F

lemma brown_nonempty (hcof : ∀ x : C, Cofibrant cof x) {x z : C} (F : x ⟶ z) :
    Nonempty (Brown (W := W) (cof := cof) F) := by
  have := hasPushout (W := W) (cof := cof) (initial.to z) (initial.to x) (hcof z)
  have hP := IsPushout.of_hasPushout (initial.to z) (initial.to x)
  obtain ⟨p, c, α, hc, hα, hcα⟩ := factorisation (W := W) (cof := cof)
    (hP.desc (𝟙 z) F (Subsingleton.elim _ _))
  exact ⟨⟨_, _, _, hP, p, c, α, hc, hα, pushout_cof (W := W) hP (hcof z),
    by rw [hcα, hP.inl_desc], by rw [hcα, hP.inr_desc]⟩⟩

/-- The diagram `(c ι_x, c ι_z) : x → z̄ ← z` of a Brown factorisation. -/
@[reducible] def Brown.span {x z : C} {F : x ⟶ z} (B : Brown (W := W) (cof := cof) F) : Span W cof x z :=
  ⟨B.pt, B.ιx ≫ B.c, B.ιz ≫ B.c, cof_comp (W := W) _ _ B.hιx B.hc,
    W_of_comp_right (cof := cof) _ B.α B.hα
      (by rw [Category.assoc, B.hz]; exact W_id (cof := cof) z)⟩

/-- **The key lemma.** A diagram `(f, i) : x → ỹ ← z` together with
`ψ : ỹ → z`, `ψ i = 1_z`, `ψ f = F`, lies in the component of the diagram of
any Brown factorisation of `F`: push out `c : x ⊔ z → z̄` along
`(f, i) : x ⊔ z → ỹ`, map the pushout to `z` by `(α, ψ)`, and factor that map
by C3; both diagrams map to the result. -/
theorem arrow_brown {x z : C} {F : x ⟶ z} (B : Brown (W := W) (cof := cof) F)
    (s : Span W cof x z) (ψ : s.pt ⟶ z) (hz : s.i ≫ ψ = 𝟙 z) (hx : s.f ≫ ψ = F) :
    ∃ r : Span W cof x z, Arrow s r ∧ Arrow B.span r := by
  let h : B.S ⟶ s.pt := B.hS.desc s.i s.f (Subsingleton.elim _ _)
  have := hasPushout (W := W) (cof := cof) B.c h B.hc
  have hQ := IsPushout.of_hasPushout B.c h
  have hcond : B.c ≫ B.α = h ≫ ψ := B.hS.hom_ext
    (by rw [B.hz, B.hS.inl_desc_assoc, hz]) (by rw [B.hx, B.hS.inr_desc_assoc, hx])
  obtain ⟨R, κ, β, hκ, hβ, hκβ⟩ := factorisation (W := W) (cof := cof)
    (pushout.desc B.α ψ hcond)
  have hr : W (s.i ≫ pushout.inr B.c h ≫ κ) :=
    W_of_comp_right (cof := cof) _ β hβ (by
      rw [Category.assoc, Category.assoc, hκβ, pushout.inr_desc, hz]
      exact W_id (cof := cof) z)
  refine ⟨⟨R, s.f ≫ pushout.inr B.c h ≫ κ, s.i ≫ pushout.inr B.c h ≫ κ,
    cof_comp (W := W) _ _ s.hf (cof_comp (W := W) _ _ (pushout_cof (W := W) hQ B.hc) hκ), hr⟩,
    ⟨pushout.inr B.c h ≫ κ, rfl, rfl⟩, ⟨pushout.inl B.c h ≫ κ, ?_, ?_⟩⟩
  · show (B.ιx ≫ B.c) ≫ _ = _
    rw [Category.assoc, pushout.condition_assoc, B.hS.inr_desc_assoc]
  · show (B.ιz ≫ B.c) ≫ _ = _
    rw [Category.assoc, pushout.condition_assoc, B.hS.inl_desc_assoc]

lemma mk_eq_brown {x z : C} {F : x ⟶ z} (B : Brown (W := W) (cof := cof) F)
    (s : Span W cof x z) (ψ : s.pt ⟶ z) (hz : s.i ≫ ψ = 𝟙 z) (hx : s.f ≫ ψ = F) :
    (Quot.mk _ s : Pi0 W cof x z) = Quot.mk _ B.span := by
  obtain ⟨r, h1, h2⟩ := arrow_brown B s ψ hz hx
  exact (Quot.sound h1).trans (Quot.sound h2).symm

/-- The class in `π₀ Ch'₀(x, z)` of a (chosen) Brown factorisation of `F`. -/
noncomputable def phiMap (hcof : ∀ x : C, Cofibrant cof x) {x z : C} (F : x ⟶ z) :
    Pi0 W cof x z :=
  Quot.mk _ (Classical.choice (brown_nonempty (W := W) hcof F)).span

/-- `φ(F)` is the class of any diagram `(f, i)` with `ψ i = 1`, `ψ f = F`. -/
lemma phiMap_eq (hcof : ∀ x : C, Cofibrant cof x) {x z : C} {F : x ⟶ z}
    (s : Span W cof x z) (ψ : s.pt ⟶ z) (hz : s.i ≫ ψ = 𝟙 z) (hx : s.f ≫ ψ = F) :
    phiMap (W := W) hcof F = Quot.mk _ s :=
  (mk_eq_brown _ s ψ hz hx).symm

variable (W cof) in
/-- The functor `𝒞 → 𝒞̃'`, `F ↦` the class of a Brown factorisation of `F`. -/
noncomputable def phi (hcof : ∀ x : C, Cofibrant cof x) : C ⥤ Rect W cof where
  obj x := ⟨x⟩
  map F := phiMap hcof F
  map_id x := phiMap_eq hcof (idSpan x) (𝟙 x) (Category.comp_id _) (Category.comp_id _)
  map_comp {x y z} f g := by
    let Bf := Classical.choice (brown_nonempty (W := W) hcof f)
    let Bg := Classical.choice (brown_nonempty (W := W) hcof g)
    show phiMap hcof (f ≫ g) = Quot.mk _ (Bf.span.comp Bg.span)
    have := hasPushout (W := W) (cof := cof) Bg.span.f Bf.span.i Bg.span.hf
    have hcond : Bg.span.f ≫ Bg.α = Bf.span.i ≫ Bf.α ≫ g := by
      show (Bg.ιx ≫ Bg.c) ≫ _ = (Bf.ιz ≫ Bf.c) ≫ _
      rw [Category.assoc, Bg.hx, Category.assoc, ← Category.assoc Bf.c, ← Category.assoc,
        Bf.hz, Category.id_comp]
    refine phiMap_eq hcof _ (pushout.desc Bg.α (Bf.α ≫ g) hcond) ?_ ?_
    · show (Bg.span.i ≫ pushout.inl _ _) ≫ _ = _
      rw [Category.assoc, pushout.inl_desc]
      show (Bg.ιz ≫ Bg.c) ≫ _ = _
      rw [Category.assoc, Bg.hz]
    · show (Bf.span.f ≫ pushout.inr _ _) ≫ _ = _
      rw [Category.assoc, pushout.inr_desc]
      show (Bf.ιx ≫ Bf.c) ≫ _ = _
      have := Bf.hx
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]

lemma phi_map_cof (hcof : ∀ x : C, Cofibrant cof x) {x y : C} (g : x ⟶ y) (hg : cof g) :
    (phi W cof hcof).map g = Quot.mk _ (cofSpan (W := W) g hg) :=
  phiMap_eq hcof _ (𝟙 y) (Category.comp_id _) (Category.comp_id _)

/-- `(1, w) ∘ (c ι_y, c ι_ỹ) = 1` for a Brown factorisation of `w ∈ W`. -/
lemma mk_back_comp_brown (hcof : ∀ x : C, Cofibrant cof x) {y y' : C} (w : y ⟶ y') (hw : W w)
    (B : Brown (W := W) (cof := cof) w) :
    (Quot.mk _ ((backSpan (cof := cof) w hw).comp B.span) : Pi0 W cof y' y') =
      Quot.mk _ (idSpan y') := by
  have := hasPushout (W := W) (cof := cof) B.span.f (backSpan (cof := cof) w hw).i B.span.hf
  have hcond : B.span.f ≫ B.α = (backSpan (cof := cof) w hw).i ≫ 𝟙 y' := by
    simp only [Category.assoc, Category.comp_id]
    exact B.hx
  let B' := Classical.choice (brown_nonempty (W := W) hcof (𝟙 y'))
  refine (mk_eq_brown B' _ (pushout.desc B.α (𝟙 y') hcond) ?_ ?_).trans
    (mk_eq_brown B' (idSpan y') (𝟙 y') (Category.comp_id _) (Category.comp_id _)).symm
  · simp only [Category.assoc, pushout.inl_desc]
    exact B.hz
  · simp only [Category.id_comp, pushout.inr_desc]

/-- `(1, w) ∘ φ(w) = 1` for every `w ∈ W`. -/
lemma back_comp_phi (hcof : ∀ x : C, Cofibrant cof x) {y y' : C} (w : y ⟶ y') (hw : W w) :
    (Quot.mk _ (backSpan (cof := cof) w hw) : (⟨y'⟩ : Rect W cof) ⟶ ⟨y⟩) ≫
      (phi W cof hcof).map w = 𝟙 _ :=
  mk_back_comp_brown hcof w hw _

/-- `φ` inverts `W₀ = W ∩ cof`: for `g ∈ W₀`, `φ(g) = (g, 1)` has inverse `(1, g)`. -/
lemma phi_inverts_W₀ (hcof : ∀ x : C, Cofibrant cof x) :
    (W ⊓ cof).IsInvertedBy (phi W cof hcof) := by
  intro x y g ⟨hgW, hg⟩
  refine ⟨⟨Quot.mk _ (backSpan (cof := cof) g hgW), ?_, back_comp_phi hcof g hgW⟩⟩
  rw [phi_map_cof hcof g hg]
  exact (Quot.sound (arrow_cof_back g hg hgW)).symm

/-- `φ` inverts `W` (page 11's argument, `inverse_W_of_inverse_W₀`). -/
lemma phi_inverts (hcof : ∀ x : C, Cofibrant cof x) : W.IsInvertedBy (phi W cof hcof) :=
  inverse_W_of_inverse_W₀ (W := W) hcof _ (phi_inverts_W₀ hcof)

variable (W cof) in
/-- The functor `q' : 𝒞̃' → W⁻¹𝒞` of page 15, `(f, i) ↦ [i]⁻¹[f]`. -/
noncomputable def qFunctor : Rect W cof ⥤ W.Localization where
  obj X := W.Q.obj X.as
  map φ := qbar φ
  map_id X := by
    show frac (idSpan X.as) = _
    exact (frac_of_retraction _ (𝟙 X.as) (𝟙 X.as) (Category.comp_id _)
      (Category.comp_id _)).trans (W.Q.map_id _)
  map_comp {X Y Z} φ ψ := by
    induction φ using Quot.ind with
    | mk s =>
    induction ψ using Quot.ind with
    | mk t =>
    show frac (s.comp t) = frac s ≫ frac t
    have := hasPushout (W := W) (cof := cof) t.f s.i t.hf
    unfold frac
    have := W.Q_inverts _ (s.comp t).hi
    rw [← cancel_mono (W.Q.map (s.comp t).i), Category.assoc, wInv_hom, Category.comp_id]
    show W.Q.map (s.f ≫ pushout.inr t.f s.i) = _ ≫ W.Q.map (t.i ≫ pushout.inl t.f s.i)
    simp only [Category.assoc, Functor.map_comp, wInv_hom_assoc]
    rw [← W.Q.map_comp t.f, pushout.condition (f := t.f) (g := s.i), W.Q.map_comp,
      wInv_hom_assoc]

variable (W cof) in
/-- The lift `φ̄ : W⁻¹𝒞 → 𝒞̃'` of `φ`. -/
noncomputable def phiBar (hcof : ∀ x : C, Cofibrant cof x) : W.Localization ⥤ Rect W cof :=
  Localization.Construction.lift (phi W cof hcof) (phi_inverts hcof)

lemma phiBar_map_Q (hcof : ∀ x : C, Cofibrant cof x) {x y : C} (f : x ⟶ y) :
    (phiBar W cof hcof).map (W.Q.map f) = (phi W cof hcof).map f := by
  refine (Functor.congr_hom (Localization.Construction.fac (phi W cof hcof)
    (phi_inverts hcof)) f).trans ?_
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- `φ̄(q'(f, i)) = (f, i)`: every arrow of `𝒞̃'` is `(1, i) ∘ (f, 1)`, with
`(f, 1) = φ(f)` and `(1, i) = φ(i)⁻¹`. -/
lemma phiBar_frac (hcof : ∀ x : C, Cofibrant cof x) {x y : C} (s : Span W cof x y) :
    (phiBar W cof hcof).map s.frac = (Quot.mk _ s : (⟨x⟩ : Rect W cof) ⟶ ⟨y⟩) := by
  have hI := phi_inverts hcof s.i s.hi
  have hinv : (phiBar W cof hcof).map (Localization.Construction.wInv s.i s.hi) =
      Quot.mk _ (backSpan (cof := cof) s.i s.hi) := by
    have h1 : (phiBar W cof hcof).map (Localization.Construction.wInv s.i s.hi) ≫
        (phiBar W cof hcof).map (W.Q.map s.i) = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, wInv_hom, CategoryTheory.Functor.map_id]
    rw [phiBar_map_Q] at h1
    exact (cancel_mono ((phi W cof hcof).map s.i)).1 (h1.trans (back_comp_phi hcof s.i s.hi).symm)
  rw [frac, Functor.map_comp, phiBar_map_Q, hinv, phi_map_cof hcof s.f s.hf]
  exact (Quot.sound (arrow_decomp s)).symm

/-- **`q'` is faithful**: when every object is cofibrant, two diagrams of
`Ch'₀(x, y)` with the same fraction `[i]⁻¹[f]` lie in the same component. -/
theorem fidele (hcof : ∀ x : C, Cofibrant cof x) (x y : C) :
    Function.Injective (qbar (W := W) (cof := cof) (x := x) (y := y)) := by
  intro a b hab
  induction a using Quot.ind with
  | mk s =>
  induction b using Quot.ind with
  | mk t =>
  have := congrArg (phiBar W cof hcof).map (show s.frac = t.frac from hab)
  rwa [phiBar_frac, phiBar_frac] at this

/-- **`(⋆⋆)` holds** when every object is cofibrant (necessity applied to `fidele`). -/
theorem critere (hcof : ∀ x : C, Cofibrant cof x) : Critere W cof :=
  critere_of_fidele (fidele hcof)

/-- **The final statement of page 15, as the finding states it**: when every
object is cofibrant, `q'` is faithful if and only if `(⋆⋆)` holds. (Both sides
hold: `fidele`, `critere`.) -/
theorem fidele_iff_critere (hcof : ∀ x : C, Cofibrant cof x) :
    (∀ x y : C, Function.Injective (qbar (W := W) (cof := cof) (x := x) (y := y))) ↔
      Critere W cof :=
  ⟨critere_of_fidele, fun _ => fidele hcof⟩

/-- **`q' : 𝒞̃' → W⁻¹𝒞` is an isomorphism of categories** when every object is
cofibrant: `φ̄` is its inverse, as equalities of functors. -/
theorem qFunctor_iso (hcof : ∀ x : C, Cofibrant cof x) :
    qFunctor W cof ⋙ phiBar W cof hcof = 𝟭 _ ∧ phiBar W cof hcof ⋙ qFunctor W cof = 𝟭 _ := by
  constructor
  · refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y φ
    induction φ using Quot.ind with
    | mk s =>
    rw [Functor.comp_map, Functor.id_map]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    exact phiBar_frac hcof s
  · apply Localization.Construction.uniq
    rw [← Functor.assoc]
    unfold phiBar
    rw [Localization.Construction.fac]
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y F
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    let B := Classical.choice (brown_nonempty (W := W) hcof F)
    show frac B.span = _
    exact frac_of_retraction _ B.α F (by show (B.ιz ≫ B.c) ≫ B.α = 𝟙 _; rw [Category.assoc, B.hz])
      (by show (B.ιx ≫ B.c) ≫ B.α = F; rw [Category.assoc, B.hx])

/-- **`q'` is full**: every arrow of `W⁻¹𝒞(x, y)` is a fraction `[i]⁻¹[f]` with
`f ∈ cof`, `i ∈ W`. -/
theorem plein (hcof : ∀ x : C, Cofibrant cof x) (x y : C) :
    Function.Surjective (qbar (W := W) (cof := cof) (x := x) (y := y)) := by
  intro φ
  refine ⟨(phiBar W cof hcof).map φ, ?_⟩
  have := Functor.congr_hom (qFunctor_iso (W := W) hcof).2 φ
  refine this.trans ?_
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end CategorieACofibrations

end Grothendieck.Folder106
