module

public import Mathlib
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Category.FGModuleCat.Basic

@[expose] public section


/-!
# Grothendieck, plan « Motifs » (IHÉS 2ILL5), pp. 2–3: « serein » means dualizable

Folder 2ILL5 of the Fonds Grothendieck–Illusie (IHÉS) holds a plan for the theory of motives. On
pp. 2–3 an object `F` of a tensor category is called « serein » when `F^∨ ⊗ F ≅ End F`, where
`F^∨ = Hom(F, 𝟙)` and `End F = Hom(F, F)` are internal Homs. The page gives the definition, not
a proof that it is the usual one; the transcription was not used here, only that statement.

The usual notion is *dualizable* (Dold–Puppe 1980; Lewis–May–Steinberger, *Equivariant stable
homotopy theory*, LNM 1213, III.1.3): `F` has a dual `Y`, with `η : 𝟙 ⟶ Y ⊗ F`,
`ε : F ⊗ Y ⟶ 𝟙` and the two triangle identities (Mathlib's `ExactPairing Y F`). The two agree,
when « ≅ » is read as « the canonical map is an isomorphism »: in a monoidal category `C` in which
`F` is closed (`Closed F`, the internal Hom `ihom F` exists), put `F^∨ = (ihom F).obj 𝟙`,
`ev : F ⊗ F^∨ ⟶ 𝟙` the evaluation, and `ν_X : F^∨ ⊗ X ⟶ (ihom F).obj X` the transpose of
`F ⊗ (F^∨ ⊗ X) ≅ (F ⊗ F^∨) ⊗ X ⟶ 𝟙 ⊗ X ≅ X`; then

* `exists_exactPairing_iff_isIso_endMap`: `F` has a (left) dual iff `ν_F : F^∨ ⊗ F ⟶ End F`
  is an isomorphism — both directions;
* `isIso_endMap_iff_forall`: and then every `ν_X` is an isomorphism;
* `exactPairingOfIsIso`: when `ν_F` is invertible, `F^∨` itself is the dual, with evaluation
  `ev` and coevaluation `𝟙 ⟶ End F ⟶ F^∨ ⊗ F` (the identity followed by `ν_F⁻¹`);
* `isIso_canonicalMap_of_exactPairing`: conversely, any dual `Y` of `F` makes all `ν_X`
  invertible (and `Y ≅ F^∨`);
* `exists_exactPairing_right_iff_isIso_endMap`: in a braided category, the same with the dual
  on the other side, so left and right dualizability and « serein » coincide;
* the sanity example at the end: in `FGModuleCat K`, `K` a field, every object is « serein ».

No braiding or symmetry is needed for the main equivalence: with Mathlib's convention
(`tensorLeft F ⊣ ihom F`) the internal dual `F^∨` is a *left* dual. The only nontrivial point is
the second triangle identity in the converse direction, which is derived from the first through the
universal property of `F^∨` (`triangle_two`).

Not formalised: that 2ILL5's « ≅ » is the canonical map (an abstract isomorphism
`F^∨ ⊗ F ≅ End F` is weaker in general; the plan does not say which is meant); anything else on
these pages; finite free modules over an arbitrary commutative ring (only vector spaces of finite
dimension, the case Mathlib supplies as a rigid category).
-/

namespace Grothendieck.Ihes2ILL5

open CategoryTheory MonoidalCategory MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- The internal dual `F^∨ = [F, 𝟙]`. -/
abbrev dual (F : C) [Closed F] : C := (ihom F).obj (𝟙_ C)

/-- The evaluation `F ⊗ F^∨ ⟶ 𝟙`. -/
def ev (F : C) [Closed F] : F ⊗ dual F ⟶ 𝟙_ C := (ihom.ev F).app (𝟙_ C)

/-- For a pairing `e : F ⊗ D ⟶ 𝟙`, the map `D ⊗ X ⟶ [F, X]` transposed from
`F ⊗ (D ⊗ X) ≅ (F ⊗ D) ⊗ X ⟶ 𝟙 ⊗ X ≅ X`. -/
def comparison {F D : C} [Closed F] (e : F ⊗ D ⟶ 𝟙_ C) (X : C) : D ⊗ X ⟶ (ihom F).obj X :=
  curry ((α_ F D X).inv ≫ e ▷ X ≫ (λ_ X).hom)

/-- The transpose of `comparison e X` is the map it was defined from. -/
lemma uncurry_comparison {F D : C} [Closed F] (e : F ⊗ D ⟶ 𝟙_ C) (X : C) :
    uncurry (comparison e X) = (α_ F D X).inv ≫ e ▷ X ≫ (λ_ X).hom := by
  simp [comparison]

/-- Changing the pairing along `h : D' ⟶ D` precomposes `comparison` with `h ▷ X`. -/
lemma comparison_precomp {F D D' : C} [Closed F] (h : D' ⟶ D) (e : F ⊗ D ⟶ 𝟙_ C) (X : C) :
    comparison (F ◁ h ≫ e) X = h ▷ X ≫ comparison e X := by
  rw [comparison, comparison, ← curry_natural_left]
  congr 1
  simp only [comp_whiskerRight, Category.assoc, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc]

/-- The canonical map `ν_X : F^∨ ⊗ X ⟶ [F, X]`. -/
def canonicalMap (F : C) [Closed F] (X : C) : dual F ⊗ X ⟶ (ihom F).obj X :=
  comparison (ev F) X

/-- The canonical map `ν_F : F^∨ ⊗ F ⟶ End F = [F, F]`; « serein » asks that it be invertible. -/
abbrev endMap (F : C) [Closed F] : dual F ⊗ F ⟶ (ihom F).obj F := canonicalMap F F

/-- For an exact pairing `(D, F)`, the inverse of `comparison`:
`[F, X] ≅ 𝟙 ⊗ [F, X] ⟶ (D ⊗ F) ⊗ [F, X] ≅ D ⊗ (F ⊗ [F, X]) ⟶ D ⊗ X`. -/
def comparisonInv (D F : C) [Closed F] [ExactPairing D F] (X : C) :
    (ihom F).obj X ⟶ D ⊗ X :=
  (λ_ _).inv ≫ η_ D F ▷ _ ≫ (α_ _ _ _).hom ≫ D ◁ (ihom.ev F).app X

/-- `comparison ≫ comparisonInv = 𝟙`: the triangle identity on `D`, whiskered by `X`. -/
theorem comparison_comp_comparisonInv (D F : C) [Closed F] [ExactPairing D F] (X : C) :
    comparison (ε_ D F) X ≫ comparisonInv D F X = 𝟙 (D ⊗ X) := by
  have h : F ◁ comparison (ε_ D F) X ≫ (ihom.ev F).app X =
      (α_ F D X).inv ≫ ε_ D F ▷ X ≫ (λ_ X).hom := by
    rw [← uncurry_eq, uncurry_comparison]
  calc _ = (λ_ _).inv ≫ η_ D F ▷ _ ≫ (α_ _ _ _).hom ≫
        D ◁ (F ◁ comparison (ε_ D F) X ≫ (ihom.ev F).app X) := by
          simp only [comparisonInv, MonoidalCategory.whiskerLeft_comp]
          rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
            associator_naturality_right_assoc]
    _ = 𝟙 (D ⊗ X) ⊗≫ (η_ D F ▷ D ⊗≫ D ◁ ε_ D F) ▷ X ⊗≫ 𝟙 (D ⊗ X) := by
          rw [h]; monoidal
    _ = 𝟙 _ := by
          rw [ExactPairing.evaluation_coevaluation'']; monoidal

/-- `comparisonInv ≫ comparison = 𝟙`, checked on transposes: the triangle identity on `F`,
whiskered by `[F, X]`. -/
theorem comparisonInv_comp_comparison (D F : C) [Closed F] [ExactPairing D F] (X : C) :
    comparisonInv D F X ≫ comparison (ε_ D F) X = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_comparison, uncurry_id_eq_ev]
  calc _ = 𝟙 (F ⊗ (ihom F).obj X) ⊗≫ (F ◁ η_ D F ⊗≫ ε_ D F ▷ F) ▷ (ihom F).obj X ⊗≫
        (show F ⊗ (ihom F).obj X ⟶ X from (ihom.ev F).app X) := by
          simp only [comparisonInv, MonoidalCategory.whiskerLeft_comp, Category.assoc]
          rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
            leftUnitor_naturality]
          monoidal
    _ = _ := by
          rw [ExactPairing.coevaluation_evaluation'']; monoidal

/-- For an exact pairing `(D, F)`, every `D ⊗ X ⟶ [F, X]` is an isomorphism: `D ⊗ -` is a
right adjoint of `F ⊗ -`, as `[F, -]` is. -/
instance isIso_comparison (D F : C) [Closed F] [ExactPairing D F] (X : C) :
    IsIso (comparison (ε_ D F) X) :=
  ⟨⟨comparisonInv D F X, comparison_comp_comparisonInv D F X,
    comparisonInv_comp_comparison D F X⟩⟩

/-- With `ev` as evaluation, any `η` satisfying the first triangle identity satisfies the
second: both sides are maps `F^∨ ⟶ F^∨`, compared through their transposes. -/
theorem triangle_two (F : C) [Closed F] (η : 𝟙_ C ⟶ dual F ⊗ F)
    (h₁ : F ◁ η ≫ (α_ _ _ _).inv ≫ ev F ▷ F = (ρ_ F).hom ≫ (λ_ F).inv) :
    η ▷ dual F ≫ (α_ _ _ _).hom ≫ dual F ◁ ev F = (λ_ _).hom ≫ (ρ_ _).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq]
  change _ ≫ ev F = _ ≫ ev F
  have h₁' : F ◁ η ⊗≫ ev F ▷ F = (ρ_ F).hom ≫ (λ_ F).inv := by rw [← h₁]; monoidal
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  calc _ = 𝟙 _ ⊗≫ (F ◁ η ⊗≫ ev F ▷ F) ▷ dual F ⊗≫ ev F := by
          have hρ : F ◁ (ρ_ (dual F)).hom ≫ ev F =
              (α_ F (dual F) (𝟙_ C)).inv ≫ (ρ_ (F ⊗ dual F)).hom ≫ ev F := by
            rw [← Category.assoc]; congr 1; monoidal
          rw [hρ, associator_inv_naturality_right_assoc, ← rightUnitor_naturality,
            whisker_exchange_assoc, ← unitors_equal, leftUnitor_naturality]
          monoidal
    _ = _ := by rw [h₁']; monoidal

/-- When `ν_F` is invertible: `𝟙 ⟶ End F ⟶ F^∨ ⊗ F`, the identity of `F` followed by `ν_F⁻¹`. -/
noncomputable def coev (F : C) [Closed F] [IsIso (endMap F)] : 𝟙_ C ⟶ dual F ⊗ F :=
  curry (ρ_ F).hom ≫ inv (endMap F)

/-- The first triangle identity for `(coev F, ev F)`: transpose `coev F ≫ ν_F = id_F`. -/
theorem triangle_one (F : C) [Closed F] [IsIso (endMap F)] :
    F ◁ coev F ≫ (α_ _ _ _).inv ≫ ev F ▷ F = (ρ_ F).hom ≫ (λ_ F).inv := by
  have h : uncurry (coev F ≫ endMap F) = (ρ_ F).hom := by
    simp [coev]
  rw [uncurry_natural_left, endMap, canonicalMap, uncurry_comparison] at h
  rw [Iso.eq_comp_inv]
  simpa only [Category.assoc] using h

/-- **« serein » ⇒ dualizable.** If `ν_F` is invertible, `(F^∨, F)` is an exact pairing with
evaluation `ev F`. -/
@[instance_reducible]
noncomputable def exactPairingOfIsIso (F : C) [Closed F] [IsIso (endMap F)] :
    ExactPairing (dual F) F where
  coevaluation' := coev F
  evaluation' := ev F
  coevaluation_evaluation' := triangle_one F
  evaluation_coevaluation' := triangle_two F _ (triangle_one F)

/-- For a dual `Y` of `F`, the isomorphism `Y ≅ Y ⊗ 𝟙 ⟶ F^∨` carries `ev` to `ε_ Y F`. -/
theorem whiskerLeft_comparison_ev (Y F : C) [Closed F] [ExactPairing Y F] :
    F ◁ ((ρ_ Y).inv ≫ comparison (ε_ Y F) (𝟙_ C)) ≫ ev F = ε_ Y F := by
  rw [ev, ← uncurry_eq, uncurry_natural_left, uncurry_comparison, unitors_equal,
    rightUnitor_naturality]
  simp

/-- **Dualizable ⇒ « serein ».** If `F` has a left dual `Y`, every canonical map
`ν_X : F^∨ ⊗ X ⟶ [F, X]` is an isomorphism; in particular `F^∨ ⊗ F ≅ End F`. -/
theorem isIso_canonicalMap_of_exactPairing (Y F : C) [Closed F] [ExactPairing Y F] (X : C) :
    IsIso (canonicalMap F X) := by
  let i : Y ≅ dual F := (ρ_ Y).symm ≪≫ asIso (comparison (ε_ Y F) (𝟙_ C))
  have hi : F ◁ i.hom ≫ ev F = ε_ Y F := whiskerLeft_comparison_ev Y F
  have hev : ev F = F ◁ i.inv ≫ ε_ Y F := by
    rw [← hi, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, i.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [canonicalMap, hev, comparison_precomp]
  infer_instance

/-- **2ILL5, pp. 2–3: « serein » is « dualizable ».** For `F` closed in a monoidal category,
`F` has a left dual iff the canonical map `F^∨ ⊗ F ⟶ End F` is an isomorphism
(Lewis–May–Steinberger III.1.3). -/
theorem exists_exactPairing_iff_isIso_endMap (F : C) [Closed F] :
    (∃ Y : C, Nonempty (ExactPairing Y F)) ↔ IsIso (endMap F) :=
  ⟨fun ⟨Y, ⟨_⟩⟩ => isIso_canonicalMap_of_exactPairing Y F F,
    fun _ => ⟨dual F, ⟨exactPairingOfIsIso F⟩⟩⟩

/-- The same, with Mathlib's `HasLeftDual`. -/
theorem nonempty_hasLeftDual_iff_isIso_endMap (F : C) [Closed F] :
    Nonempty (HasLeftDual F) ↔ IsIso (endMap F) := by
  rw [← exists_exactPairing_iff_isIso_endMap]
  exact ⟨fun ⟨h⟩ => ⟨h.leftDual, ⟨h.exact⟩⟩, fun ⟨Y, ⟨h⟩⟩ => ⟨⟨Y⟩⟩⟩

/-- `ν_F` is invertible iff every `ν_X` is. -/
theorem isIso_endMap_iff_forall (F : C) [Closed F] :
    IsIso (endMap F) ↔ ∀ X, IsIso (canonicalMap F X) := by
  refine ⟨fun _ X => ?_, fun h => h F⟩
  obtain ⟨Y, ⟨_⟩⟩ := (exists_exactPairing_iff_isIso_endMap F).2 ‹_›
  exact isIso_canonicalMap_of_exactPairing Y F X

section Braided

variable [BraidedCategory C]

/-- In a braided category, `F` has a right dual iff `F^∨ ⊗ F ⟶ End F` is an isomorphism; left
and right duals are exchanged by the braiding (`BraidedCategory.exactPairing_swap`). -/
theorem exists_exactPairing_right_iff_isIso_endMap (F : C) [Closed F] :
    (∃ Y : C, Nonempty (ExactPairing F Y)) ↔ IsIso (endMap F) := by
  rw [← exists_exactPairing_iff_isIso_endMap]
  exact ⟨fun ⟨Y, ⟨_⟩⟩ => ⟨Y, ⟨BraidedCategory.exactPairing_swap F Y⟩⟩,
    fun ⟨Y, ⟨_⟩⟩ => ⟨Y, ⟨BraidedCategory.exactPairing_swap Y F⟩⟩⟩

end Braided

end Grothendieck.Ihes2ILL5

section Example
open CategoryTheory Grothendieck.Ihes2ILL5

/-- Sanity check: a finite-dimensional vector space is « serein », `V^∨ ⊗ V ≅ End V`. -/
example {K : Type*} [Field K] (V : FGModuleCat K) : IsIso (endMap V) :=
  (exists_exactPairing_right_iff_isIso_endMap V).1
    ⟨FGModuleCat.FGModuleCatDual K V, ⟨inferInstance⟩⟩

end Example
