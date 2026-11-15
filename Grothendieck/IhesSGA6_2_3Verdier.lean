module

public import Mathlib
public import Grothendieck.IhesSGA6_2_3
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Algebra.Exact.Basic

@[expose] public section


/-!
# IHÉS FG_IL_5_SGA6_2_3, view 3: `K(D) → K(T) → K(T/D) → 0` for a Verdier quotient

Working notes headed « Groupes K » in the Fonds Grothendieck–Illusie (IHÉS). View 3 states,
marked « à vérifier », that for a thick (« épaisse ») triangulated subcategory `D` of a
triangulated category `T` the sequence `K(D) → K(T) → K(T/D) → 0` is exact.

Here `T` is a triangulated category in the sense of mathlib (`IsTriangulated T`: the octahedral
axiom is used, through mathlib's calculus of fractions for `P.trW`), `D` is given by
`P : ObjectProperty T` with `P.IsTriangulated` and `P.IsStableUnderRetracts` (thick), and the
Verdier quotient is any localization functor `L : T ⥤ Q` for `P.trW` (morphisms whose cone lies
in `D`) which is a triangulated functor to a pretriangulated category; mathlib's
`P.trW.Localization` is one (`exact_localization` below). `K₀ C` is `FreeAbelianGroup C`
modulo the relations `[Y] − [X] − [Z]` of the distinguished triangles, as defined in
`Grothendieck/IhesSGA6_2_3.lean`, which this file imports; mathlib has no `K₀` of a triangulated
category.

**What is proved.**
* `map_surjective`: `K(T) → K(T/D)` is surjective, every object of `T/D` being isomorphic to some
  `L X`. Only `L` essentially surjective is used.
* `map_comp_map_ι`: the composite `K(D) → K(T) → K(T/D)` is zero, since `L X ≅ L 0` for `X ∈ D`.
  No thickness is used.
* `isZero_map_iff`: `L X ≅ 0` if and only if `X ∈ D` — this is where thickness enters: a
  zero morphism `X → Y` in `P.trW` has cone `Y ⊞ X[1]`, so `X[1]` is a direct summand of an
  object of `D`.
* `cl_sub_cl_mem_range_of_iso`: `L X ≅ L Y` implies `cl X − cl Y ∈ im K(D)`, through a left
  fraction `X → Y' ← Y` and the cones of its two arrows.
* `descQuotient`, `descQuotient_map`: the map `K(T/D) → K(T)/im K(D)`, `cl (L X) ↦ [X]`.
* `ker_map_eq_range`: **the exactness in the middle**, `ker (K(T) → K(T/D)) = im (K(D) → K(T))`.
* `exact`: the statement of view 3, `Function.Exact (K(ι)) (K(L))` and `K(L)` surjective.

**On « épaisse ».** Thickness is needed for exactness in the middle, not only for the
Verdier quotient to be « the right one ». Without it `T/D = T/D̄` with `D̄` the thick closure,
while the image of `K(D)` can be smaller than that of `K(D̄)`: for `T = D^b(k)` and `D` the
complexes of even Euler characteristic (a dense, non-thick triangulated subcategory), `T/D = 0`
but `K(D) → K(T) = ℤ` has image `2ℤ` (Thomason, Compositio 105, 1997, Th. 2.1). The
counter-example is not formalised here. Surjectivity and the vanishing of the composite hold for
any triangulated `D`.
-/

namespace Grothendieck.IhesSGA6_2_3

open CategoryTheory Limits Pretriangulated ZeroObject

section Verdier

universe v₁ v₂ u₁ u₂

variable {T : Type u₁} [Category.{v₁} T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  {Q : Type u₂} [Category.{v₂} Q] [HasZeroObject Q] [HasShift Q ℤ] [Preadditive Q]
  [∀ n : ℤ, (shiftFunctor Q n).Additive] [Pretriangulated Q]
  (P : ObjectProperty T) [P.IsTriangulated]
  (L : T ⥤ Q) [L.CommShift ℤ] [L.IsTriangulated]

/-- The image of `K(D) → K(T)`, for `D` the full subcategory of the objects satisfying `P`. -/
noncomputable abbrev imageK : AddSubgroup (K₀ T) := (map P.ι).range

theorem cl_mem_imageK {X : T} (hX : P X) : cl X ∈ imageK P :=
  ⟨cl (⟨X, hX⟩ : P.FullSubcategory), map_cl _ _⟩

/-- **Surjectivity** of `K(T) → K(T/D)`: every object of the quotient is some `L X` up to
isomorphism, and `cl` is onto. -/
theorem map_surjective [L.EssSurj] : Function.Surjective (map L) := by
  intro y
  obtain ⟨Y, rfl⟩ := cl_surjective y
  exact ⟨cl (L.objPreimage Y), by rw [map_cl, cl_eq_of_iso (L.objObjPreimageIso Y)]⟩

/-- **The composite `K(D) → K(T) → K(T/D)` is zero**: for `X ∈ D` the morphism `X → 0` has cone
`X[1] ∈ D`, so `L X ≅ L 0 = 0`. Thickness is not used. -/
theorem map_comp_map_ι [L.IsLocalization P.trW] : (map L).comp (map P.ι) = 0 := by
  refine hom_ext fun X => ?_
  have hW : P.trW (0 : X.obj ⟶ 0) :=
    ObjectProperty.trW.mk' P (contractible_distinguished X.obj) X.property
  have := Localization.inverts L P.trW _ hW
  simp only [AddMonoidHom.comp_apply, map_cl, AddMonoidHom.zero_apply]
  change cl (L.obj X.obj) = 0
  rw [cl_eq_of_iso (asIso (L.map (0 : X.obj ⟶ 0))), cl_of_isZero (L.map_isZero (isZero_zero T))]

variable [IsTriangulated T] [L.IsLocalization P.trW]

/-- An object becomes zero in `T/D` exactly when it lies in `D`, for `D` thick. If `L X ≅ 0`,
then `L (𝟙 X) = L 0`, so some `s : X → Y` in `P.trW` has `s = 𝟙 ≫ s = 0 ≫ s = 0`; the cone of a
zero morphism `X → Y` is `Y ⊞ X[1]`, hence `X[1]`, a summand of an object of `D`, is in `D`. -/
theorem isZero_map_iff [P.IsStableUnderRetracts] (X : T) : IsZero (L.obj X) ↔ P X := by
  constructor
  · intro hX
    have h : L.map (𝟙 X) = L.map 0 := hX.eq_of_src _ _
    obtain ⟨Y, s, ⟨Z, g, h, hT, hZ⟩, hs⟩ :=
      (MorphismProperty.map_eq_iff_postcomp L P.trW _ _).mp h
    simp only [Category.id_comp, zero_comp] at hs
    subst hs
    have hR := rot_of_distTriang _ hT
    obtain ⟨e, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hR
      (by simp only [Triangle.rotate_mor₃, Triangle.mk_mor₁, Functor.map_zero, neg_zero]; exact rfl)
    have h₁ : P (Y ⊞ X⟦(1 : ℤ)⟧) := P.prop_of_iso e hZ
    exact (P.prop_shift_iff_of_isStableUnderShift X (1 : ℤ)).mp
      (ObjectProperty.IsStableUnderRetracts.of_biprod_right P h₁)
  · intro hX
    have hW : P.trW (0 : X ⟶ 0) :=
      ObjectProperty.trW.mk' P (contractible_distinguished X) hX
    have := Localization.inverts L P.trW _ hW
    exact (L.map_isZero (isZero_zero T)).of_iso (asIso (L.map (0 : X ⟶ 0)))

omit [IsTriangulated T] in
/-- A morphism of `P.trW` changes the class by an element of `im K(D)`. -/
theorem cl_sub_cl_mem_of_trW {X Y : T} {s : X ⟶ Y} (hs : P.trW s) : cl Y - cl X ∈ imageK P := by
  obtain ⟨Z, g, h, hT, hZ⟩ := hs
  have := cl_obj₂ _ hT
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at this
  rw [this, add_sub_cancel_left]
  exact cl_mem_imageK P hZ

/-- A morphism `f` with `L f` invertible changes the class by an element of `im K(D)`, `D`
thick: its cone becomes zero in `T/D`, so lies in `D`. -/
theorem cl_sub_cl_mem_of_isIso [P.IsStableUnderRetracts] {X Y : T} (f : X ⟶ Y)
    [IsIso (L.map f)] : cl Y - cl X ∈ imageK P := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hLT := L.map_distinguished _ hT
  have hZ : IsZero (L.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ hLT).mpr (by dsimp; infer_instance)
  have := cl_obj₂ _ hT
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃] at this
  rw [this, add_sub_cancel_left]
  exact cl_mem_imageK P ((isZero_map_iff P L Z).mp hZ)

/-- Objects of `T` that become isomorphic in `T/D` have classes congruent modulo `im K(D)`:
the isomorphism is a left fraction `X → Y' ← Y` with `Y → Y'` in `P.trW`, and `X → Y'` becomes
invertible. -/
theorem cl_sub_cl_mem_range_of_iso [P.IsStableUnderRetracts] {X Y : T} (e : L.obj X ≅ L.obj Y) :
    cl X - cl Y ∈ imageK P := by
  obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.trW e.hom
  have hs := Localization.inverts L P.trW φ.s φ.hs
  have hf : L.map φ.f = e.hom ≫ L.map φ.s := by
    rw [hφ, MorphismProperty.LeftFraction.map_comp_map_s]
  have : IsIso (L.map φ.f) := by rw [hf]; infer_instance
  have h₁ := cl_sub_cl_mem_of_isIso P L φ.f
  have h₂ := cl_sub_cl_mem_of_trW P φ.hs
  have := sub_mem h₂ h₁
  rwa [sub_sub_sub_cancel_left] at this

/-- The function `Y ↦ [X]` on the objects of `T/D`, for any `X` with `L X ≅ Y`. -/
noncomputable def descFun (Y : Q) : K₀ T ⧸ imageK P :=
  haveI := Localization.essSurj L P.trW
  QuotientAddGroup.mk (cl (L.objPreimage Y))

theorem descFun_eq [P.IsStableUnderRetracts] {X : T} {Y : Q} (e : L.obj X ≅ Y) :
    descFun P L Y = QuotientAddGroup.mk (cl X) := by
  have := Localization.essSurj L P.trW
  refine (QuotientAddGroup.eq_iff_sub_mem).mpr ?_
  exact cl_sub_cl_mem_range_of_iso P L (L.objObjPreimageIso Y ≪≫ e.symm)

/-- **The map `K(T/D) → K(T)/im K(D)`**, `cl (L X) ↦ [X]`. It is well defined because every
distinguished triangle of `T/D` is isomorphic to the image of a distinguished triangle of `T`. -/
noncomputable def descQuotient [P.IsStableUnderRetracts] : K₀ Q →+ K₀ T ⧸ imageK P :=
  lift (descFun P L) fun Δ hΔ => by
    have := Localization.essSurj_mapArrow L P.trW
    obtain ⟨Δ₀, e, hΔ₀⟩ := (L.distTriang_iff Δ).mp hΔ
    let e₁ : L.obj Δ₀.obj₁ ≅ Δ.obj₁ := Triangle.π₁.mapIso e.symm
    let e₂ : L.obj Δ₀.obj₂ ≅ Δ.obj₂ := Triangle.π₂.mapIso e.symm
    let e₃ : L.obj Δ₀.obj₃ ≅ Δ.obj₃ := Triangle.π₃.mapIso e.symm
    rw [descFun_eq P L e₁, descFun_eq P L e₂, descFun_eq P L e₃, ← QuotientAddGroup.mk_add]
    exact congrArg _ (cl_obj₂ _ hΔ₀)

theorem descQuotient_map [P.IsStableUnderRetracts] (x : K₀ T) :
    descQuotient P L (map L x) = QuotientAddGroup.mk x := by
  obtain ⟨X, rfl⟩ := cl_surjective x
  rw [map_cl, descQuotient, lift_cl, descFun_eq P L (Iso.refl _)]

/-- **Exactness in the middle**: for `D` thick, the kernel of `K(T) → K(T/D)` is the image of
`K(D) → K(T)`. -/
theorem ker_map_eq_range [P.IsStableUnderRetracts] : (map L).ker = (map P.ι).range := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have h := descQuotient_map P L x
    rw [AddMonoidHom.mem_ker.mp hx, map_zero] at h
    exact (QuotientAddGroup.eq_zero_iff x).mp h.symm
  · rintro _ ⟨y, rfl⟩
    exact AddMonoidHom.mem_ker.mpr (DFunLike.congr_fun (map_comp_map_ι P L) y)

/-- **View 3**: for a thick triangulated subcategory `D` of a triangulated category `T`, the
sequence `K(D) → K(T) → K(T/D) → 0` is exact. -/
theorem exact [P.IsStableUnderRetracts] :
    Function.Exact (map P.ι) (map L) ∧ Function.Surjective (map L) := by
  have := Localization.essSurj L P.trW
  refine ⟨fun x => ?_, map_surjective L⟩
  rw [← AddMonoidHom.mem_ker, ker_map_eq_range P L, AddMonoidHom.mem_range]
  rfl

end Verdier

section Instance

universe v u

variable {T : Type u} [Category.{v} T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  (P : ObjectProperty T) [P.IsTriangulated] [P.IsStableUnderRetracts]

/-- The statement for mathlib's own Verdier quotient `P.trW.Localization`. -/
theorem exact_localization :
    Function.Exact (map P.ι) (map P.trW.Q) ∧ Function.Surjective (map P.trW.Q) :=
  exact P P.trW.Q

end Instance

end Grothendieck.IhesSGA6_2_3
