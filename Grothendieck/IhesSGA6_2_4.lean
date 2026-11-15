module

public import Mathlib
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.Exact

@[expose] public section


/-!
# IHÉS FG_IL_5_SGA6_2_4, views 1–2: Ext-bijectivity of an exact functor by effaceability

Autograph notes of the Fonds Grothendieck–Illusie (IHÉS), FG_IL_5_SGA6_2_4, headed « Comparaison
des cat. dérivées avec Modules quelc. et Modules qu.-coh. ». The Lemme of views 1–2: for an exact
functor `φ : C → C'` of abelian categories, conditions equivalent to `D^b(φ)` being fully
faithful: (i) `Extⁿ(A, B) → Extⁿ(φA, φB)` bijective for all `A, B, n`; (ii) `D^b(φ)` fully
faithful; (i bis) the same on generators and cogenerators; (iii) `φ` fully faithful and every
`ξ ∈ Extⁿ(φA, φB)`, `n > 0`, effaced by an epimorphism `A' ↠ A` of `C`; (iv) the same with a
monomorphism `B ↪ B'`. The proof: Ext classes of positive degree in `C` are effaceable (« comme il
résulte aussitôt des définitions »), and the satellites are unique. The « Rédiger mieux » of view 2
does it for a fixed `A`: `Extⁿ(A, B) ≅ Extⁿ(φA, φB)` for all `B, n` iff `Hom(A, B) ≅ Hom(φA, φB)`
for all `B` and the positive-degree classes are effaceable in `B`.

Here `C`, `D` are abelian categories with mathlib's `Ext` (`HasExt`), `F : C ⥤ D` is additive
and exact, and the map on `Ext` is mathlib's `Ext.mapExactFunctor` (`F.mapExtAddHom`). The
effaceability of Ext in `C`, which the page takes as known, is a hypothesis (`EffaceableByMono`,
`EffaceableByEpi`): mathlib does not have it for a general abelian category; it is proved here when
`C` has enough injectives, resp. projectives.

**What is proved.**
* `bijective_of_mapEffacedByMono`: the fixed-`A` form of (iv) ⇒ (i): if `F` is bijective on
  `Hom(X, -)` and every class of `Extⁿ⁺¹(FX, FY)` is killed by `F` of a monomorphism `Y ↪ Y'`,
  then `Extⁿ(X, Y) → Extⁿ(FX, FY)` is bijective for all `Y` and `n`;
* `mapEffacedByMono_of_bijective`, `bijective_iff_mapEffacedByMono`: the converse and the
  equivalence (i) ⇔ (iv), for a fixed `X`, given `EffaceableByMono C`;
* `bijective_of_mapEffacedByEpi`, `mapEffacedByEpi_of_bijective`, `bijective_iff_mapEffacedByEpi`:
  the dual, (i) ⇔ (iii), for a fixed `Y`, given `EffaceableByEpi C`;
* `forall_bijective_iff_mono`, `forall_bijective_iff_epi`: the Lemme's (i) ⇔ (iii) ⇔ (iv) for all
  objects;
* `effaceableByMono_of_enoughInjectives`, `effaceableByEpi_of_enoughProjectives`.

**More generally.** The fixed-object form is the « Rédiger mieux » statement, and it contains
mathlib's `Functor.mapExt_bijective_of_preservesInjectiveObjects`: when `F` preserves injectives,
`F` of a monomorphism into an injective effaces every class. The induction is the uniqueness of
satellites, with mathlib's long exact sequences of `Ext`.

**Not formalised.** (ii) and its equivalence with (i) (the « dévissage », through the bounded
derived category, which mathlib does not single out); (i bis), (iii bis), (iv bis) on generators
and cogenerators; the description of the essential image of `D^b(φ)`; the effaceability of Ext in
an arbitrary abelian category; the rest of the item (quasi-coherent sheaves, views 3–11).
-/

namespace Grothendieck.IhesSGA6_2_4

open CategoryTheory Limits Abelian Function

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

section Defs

variable (C) [HasExt.{w} C]

/-- Every class of positive degree in `Ext(X, Y)` is killed by a monomorphism `Y ↪ Y'`. -/
def EffaceableByMono : Prop :=
  ∀ (X Y : C) (n : ℕ) (ζ : Ext.{w} X Y (n + 1)),
    ∃ (Y' : C) (i : Y ⟶ Y'), Mono i ∧ ζ.comp (Ext.mk₀ i) (add_zero _) = 0

/-- Every class of positive degree in `Ext(X, Y)` is killed by an epimorphism `X' ↠ X`. -/
def EffaceableByEpi : Prop :=
  ∀ (X Y : C) (n : ℕ) (ζ : Ext.{w} X Y (n + 1)),
    ∃ (X' : C) (π : X' ⟶ X), Epi π ∧ (Ext.mk₀ π).comp ζ (zero_add _) = 0

theorem effaceableByMono_of_enoughInjectives [EnoughInjectives C] : EffaceableByMono.{w} C :=
  fun _ Y _ _ => ⟨Injective.under Y, Injective.ι Y, inferInstance, Ext.eq_zero_of_injective _⟩

theorem effaceableByEpi_of_enoughProjectives [EnoughProjectives C] : EffaceableByEpi.{w} C :=
  fun X _ _ _ => ⟨Projective.over X, Projective.π X, inferInstance, Ext.eq_zero_of_projective _⟩

end Defs

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- Condition (iv) for a fixed `X`: every class of `Extⁿ⁺¹(FX, FY)` is killed by `F` of a
monomorphism `Y ↪ Y'` of `C`. -/
def MapEffacedByMono (X : C) : Prop :=
  ∀ (Y : C) (n : ℕ) (ξ : Ext.{w'} (F.obj X) (F.obj Y) (n + 1)),
    ∃ (Y' : C) (i : Y ⟶ Y'), Mono i ∧ ξ.comp (Ext.mk₀ (F.map i)) (add_zero _) = 0

/-- Condition (iii) for a fixed `Y`: every class of `Extⁿ⁺¹(FX, FY)` is killed by `F` of an
epimorphism `X' ↠ X` of `C`. -/
def MapEffacedByEpi (Y : C) : Prop :=
  ∀ (X : C) (n : ℕ) (ξ : Ext.{w'} (F.obj X) (F.obj Y) (n + 1)),
    ∃ (X' : C) (π : X' ⟶ X), Epi π ∧ (Ext.mk₀ (F.map π)).comp ξ (zero_add _) = 0

theorem bijective_zero_iff (X Y : C) :
    Bijective (F.mapExtAddHom.{w, w'} X Y 0) ↔ Bijective (F.map : (X ⟶ Y) → _) := by
  rw [Functor.mapExtAddHom_coe, Ext.mapExactFunctor₀]
  exact (Equiv.comp_bijective _ _).trans (Equiv.bijective_comp _ _)

/-- **(iv) ⇒ (i)**, for a fixed `X` (the « Rédiger mieux » of view 2). -/
theorem bijective_of_mapEffacedByMono (hC : EffaceableByMono.{w} C) (X : C)
    (h0 : ∀ Y, Bijective (F.map : (X ⟶ Y) → _)) (hX : MapEffacedByMono.{w'} F X) :
    ∀ (n : ℕ) (Y : C), Bijective (F.mapExtAddHom.{w, w'} X Y n) := by
  intro n
  induction n with
  | zero => exact fun Y => (bijective_zero_iff F X Y).2 (h0 Y)
  | succ n ih =>
    intro Y
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro ζ hζ
      obtain ⟨Y', i, hi, hiζ⟩ := hC X Y n ζ
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      obtain ⟨y₃, hy₃⟩ := Ext.covariant_sequence_exact₁ X hS ζ hiζ rfl
      have h1 : (y₃.mapExactFunctor F).comp (hS.map_of_exact F).extClass rfl = 0 := by
        rw [← Ext.mapExactFunctor_extClass F hS, ← Ext.mapExactFunctor_comp, hy₃]
        exact hζ
      obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ (F.obj X) (hS.map_of_exact F) _ rfl h1
      obtain ⟨y₂, rfl⟩ := (ih Y').2 x₂
      have h2 : y₂.comp (Ext.mk₀ S.g) (add_zero n) = y₃ := by
        apply (ih _).1
        rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
          Ext.mapExactFunctor_mk₀]
        exact hx₂
      rw [← hy₃, ← h2, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
    · intro ξ
      obtain ⟨Y', i, hi, hiξ⟩ := hX Y n ξ
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (F.obj X) (hS.map_of_exact F) ξ hiξ rfl
      obtain ⟨y₃, rfl⟩ := (ih _).2 x₃
      refine ⟨y₃.comp hS.extClass rfl, ?_⟩
      rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      exact hx₃

/-- **(i) ⇒ (iv)**, for a fixed `X`, given the effaceability of Ext in `C`. -/
theorem mapEffacedByMono_of_bijective (hC : EffaceableByMono.{w} C) (X : C)
    (h : ∀ (n : ℕ) (Y : C), Bijective (F.mapExtAddHom.{w, w'} X Y n)) :
    MapEffacedByMono.{w'} F X := by
  intro Y n ξ
  obtain ⟨ζ, rfl⟩ := (h (n + 1) Y).2 ξ
  obtain ⟨Y', i, hi, hζ⟩ := hC X Y n ζ
  refine ⟨Y', i, hi, ?_⟩
  rw [Functor.mapExtAddHom_apply, ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp, hζ,
    Ext.mapExactFunctor_zero]

/-- **(i) ⇔ (iv)** for a fixed `X`. -/
theorem bijective_iff_mapEffacedByMono (hC : EffaceableByMono.{w} C) (X : C) :
    (∀ (n : ℕ) (Y : C), Bijective (F.mapExtAddHom.{w, w'} X Y n)) ↔
      (∀ Y, Bijective (F.map : (X ⟶ Y) → _)) ∧ MapEffacedByMono.{w'} F X :=
  ⟨fun h => ⟨fun Y => (bijective_zero_iff F X Y).1 (h 0 Y),
      mapEffacedByMono_of_bijective F hC X h⟩,
    fun ⟨h0, hX⟩ => bijective_of_mapEffacedByMono F hC X h0 hX⟩

/-- **(iii) ⇒ (i)**, for a fixed `Y`. -/
theorem bijective_of_mapEffacedByEpi (hC : EffaceableByEpi.{w} C) (Y : C)
    (h0 : ∀ X, Bijective (F.map : (X ⟶ Y) → _)) (hY : MapEffacedByEpi.{w'} F Y) :
    ∀ (n : ℕ) (X : C), Bijective (F.mapExtAddHom.{w, w'} X Y n) := by
  intro n
  induction n with
  | zero => exact fun X => (bijective_zero_iff F X Y).2 (h0 X)
  | succ n ih =>
    intro X
    refine ⟨?_, ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro ζ hζ
      obtain ⟨X', π, hπ, hπζ⟩ := hC X Y n ζ
      let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
      obtain ⟨y₁, hy₁⟩ := Ext.contravariant_sequence_exact₃ hS Y ζ hπζ (add_comm 1 n)
      have h1 : (hS.map_of_exact F).extClass.comp (y₁.mapExactFunctor F) (add_comm 1 n) = 0 := by
        rw [← Ext.mapExactFunctor_extClass F hS, ← Ext.mapExactFunctor_comp, hy₁]
        exact hζ
      obtain ⟨x₂, hx₂⟩ :=
        Ext.contravariant_sequence_exact₁ (hS.map_of_exact F) (F.obj Y) _ (add_comm 1 n) h1
      obtain ⟨y₂, rfl⟩ := (ih X').2 x₂
      have h2 : (Ext.mk₀ S.f).comp y₂ (zero_add n) = y₁ := by
        apply (ih _).1
        rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
          Ext.mapExactFunctor_mk₀]
        exact hx₂
      rw [← hy₁, ← h2, ← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by omega) (by omega) (by omega),
        hS.extClass_comp, Ext.zero_comp]
    · intro ξ
      obtain ⟨X', π, hπ, hπξ⟩ := hY X n ξ
      let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
      obtain ⟨x₁, hx₁⟩ :=
        Ext.contravariant_sequence_exact₃ (hS.map_of_exact F) (F.obj Y) ξ hπξ (add_comm 1 n)
      obtain ⟨y₁, rfl⟩ := (ih _).2 x₁
      refine ⟨hS.extClass.comp y₁ (add_comm 1 n), ?_⟩
      rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      exact hx₁

/-- **(i) ⇒ (iii)**, for a fixed `Y`, given the effaceability of Ext in `C`. -/
theorem mapEffacedByEpi_of_bijective (hC : EffaceableByEpi.{w} C) (Y : C)
    (h : ∀ (n : ℕ) (X : C), Bijective (F.mapExtAddHom.{w, w'} X Y n)) :
    MapEffacedByEpi.{w'} F Y := by
  intro X n ξ
  obtain ⟨ζ, rfl⟩ := (h (n + 1) X).2 ξ
  obtain ⟨X', π, hπ, hζ⟩ := hC X Y n ζ
  refine ⟨X', π, hπ, ?_⟩
  rw [Functor.mapExtAddHom_apply, ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp, hζ,
    Ext.mapExactFunctor_zero]

/-- **(i) ⇔ (iii)** for a fixed `Y`. -/
theorem bijective_iff_mapEffacedByEpi (hC : EffaceableByEpi.{w} C) (Y : C) :
    (∀ (n : ℕ) (X : C), Bijective (F.mapExtAddHom.{w, w'} X Y n)) ↔
      (∀ X, Bijective (F.map : (X ⟶ Y) → _)) ∧ MapEffacedByEpi.{w'} F Y :=
  ⟨fun h => ⟨fun X => (bijective_zero_iff F X Y).1 (h 0 X),
      mapEffacedByEpi_of_bijective F hC Y h⟩,
    fun ⟨h0, hY⟩ => bijective_of_mapEffacedByEpi F hC Y h0 hY⟩

/-- The Lemme, **(i) ⇔ (iv)**: `F` induces bijections on all `Ext` iff it is fully faithful and
the classes of positive degree between images are effaced by images of monomorphisms. -/
theorem forall_bijective_iff_mono (hC : EffaceableByMono.{w} C) :
    (∀ (X Y : C) (n : ℕ), Bijective (F.mapExtAddHom.{w, w'} X Y n)) ↔
      (∀ X Y : C, Bijective (F.map : (X ⟶ Y) → _)) ∧ ∀ X, MapEffacedByMono.{w'} F X :=
  ⟨fun h => ⟨fun X Y => ((bijective_iff_mapEffacedByMono F hC X).1 (fun n Y => h X Y n)).1 Y,
      fun X => ((bijective_iff_mapEffacedByMono F hC X).1 (fun n Y => h X Y n)).2⟩,
    fun ⟨h0, hX⟩ X Y n => (bijective_iff_mapEffacedByMono F hC X).2 ⟨h0 X, hX X⟩ n Y⟩

/-- The Lemme, **(i) ⇔ (iii)**. -/
theorem forall_bijective_iff_epi (hC : EffaceableByEpi.{w} C) :
    (∀ (X Y : C) (n : ℕ), Bijective (F.mapExtAddHom.{w, w'} X Y n)) ↔
      (∀ X Y : C, Bijective (F.map : (X ⟶ Y) → _)) ∧ ∀ Y, MapEffacedByEpi.{w'} F Y :=
  ⟨fun h => ⟨fun X Y => ((bijective_iff_mapEffacedByEpi F hC Y).1 (fun n X => h X Y n)).1 X,
      fun Y => ((bijective_iff_mapEffacedByEpi F hC Y).1 (fun n X => h X Y n)).2⟩,
    fun ⟨h0, hY⟩ X Y n => (bijective_iff_mapEffacedByEpi F hC Y).2 ⟨fun X => h0 X Y, hY Y⟩ n X⟩

end Grothendieck.IhesSGA6_2_4
