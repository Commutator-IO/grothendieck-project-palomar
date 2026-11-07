module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/semiSimplexCategory-reedy`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/semiSimplexCategory-reedy`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/AlgebraicTopology/Reedy/Direct.lean` (new file) -/

/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/


/-!
# Direct categories

A category `C` is *direct* if it has a Reedy structure in which `W₁` consists of the identities
and `W₂` of all morphisms, i.e. a degree function on objects that every non-identity morphism
strictly raises.

We show that `C` is direct if and only if the relation "there is a non-identity morphism
`X ⟶ Y`" on the objects of `C` is well-founded:

* `HomotopicalAlgebra.ReedyStructure.ofWellFounded`: if this relation is well-founded, the rank
  of an object for it is a degree making `C` direct (with values in `Ordinal`);
* `HomotopicalAlgebra.ReedyStructure.wellFounded`: conversely, the relation is well-founded for
  any Reedy structure on `C` with `W₁ = identities C` and `W₂ = ⊤`.

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]
-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra.ReedyStructure

variable {C : Type u} [Category.{v} C]

/-- The only factorization of `f` as an identity followed by a morphism is `𝟙 _ ≫ f`. -/
instance {X Y : C} (f : X ⟶ Y) :
    Unique ((identities C).MapFactorizationData ⊤ f) where
  default := ⟨X, 𝟙 X, f, by simp, .mk _, trivial⟩
  uniq := by
    rintro ⟨Z, i, p, fac, hi, hp⟩
    cases hi
    simp only [Category.id_comp] at fac
    subst fac
    rfl

/-- If the relation "there is a non-identity morphism `X ⟶ Y`" on the objects of `C` is
well-founded, then `C` is a direct category: the rank of an object for this relation is a
degree that every non-identity morphism strictly raises. -/
noncomputable def ofWellFounded
    (h : WellFounded fun X Y : C => ∃ f : X ⟶ Y, ¬ identities C f) :
    ReedyStructure (identities C) ⊤ Ordinal.{u} :=
  haveI := h
  { deg := WellFounded.rank _
    lt₁ _ hf hf' := absurd hf hf'
    lt₂ f _ hf' :=
      WellFounded.rank_lt_of_rel (r := fun X Y : C => ∃ f : X ⟶ Y, ¬ identities C f) ⟨f, hf'⟩
    nonempty_unique _ := ⟨inferInstance⟩ }

variable {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]

/-- In a direct category, the relation "there is a non-identity morphism `X ⟶ Y`" on objects is
well-founded. -/
lemma wellFounded (r : ReedyStructure (identities C) ⊤ α) :
    WellFounded fun X Y : C => ∃ f : X ⟶ Y, ¬ identities C f :=
  Subrelation.wf (fun ⟨f, hf⟩ => r.lt₂ f trivial hf) (InvImage.wf r.deg wellFounded_lt)

/-- In a direct category, every endomorphism is an identity. -/
lemma eq_id_of_endo (r : ReedyStructure (identities C) ⊤ α) {X : C} (f : X ⟶ X) : f = 𝟙 X := by
  by_contra hf
  refine (r.lt₂ f trivial fun h => hf ?_).false
  cases h
  rfl

end HomotopicalAlgebra.ReedyStructure


/-! ## From `Mathlib/AlgebraicTopology/Reedy/SemiSimplexCategory.lean` (new file) -/

/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/


/-!
# The semi-simplex category is direct

The category `SemiSimplexCategory` (finite nonempty ordinals and order embeddings) is a direct
category: every non-identity morphism `⦋n⦌ₛ ⟶ ⦋m⦌ₛ` satisfies `n < m`. Hence it has a Reedy
structure `SemiSimplexCategory.reedyStructure` in which `W₁` consists of the identities and
`W₂` of all morphisms, with degree `len`.

## References
* [Emily Riehl and Dominic Verity, *Elements of ∞-Category Theory*, C.4][RiehlVerity2022]
-/

@[expose] public section

open CategoryTheory MorphismProperty HomotopicalAlgebra

open scoped Simplicial

namespace SemiSimplexCategory

/-- In `SemiSimplexCategory`, every endomorphism is an identity. -/
lemma eq_id_of_endo {n : SemiSimplexCategory} (f : n ⟶ n) : f = 𝟙 n :=
  toSimplexCategory.map_injective (by
    rw [SimplexCategory.eq_id_of_mono (toSimplexCategory.map f), CategoryTheory.Functor.map_id])

lemma len_le_of_hom {n m : SemiSimplexCategory} (f : n ⟶ m) : n.len ≤ m.len :=
  SimplexCategory.len_le_of_mono (toSimplexCategory.map f)

/-- A morphism of `SemiSimplexCategory` which is not an identity strictly increases `len`. -/
lemma len_lt_of_not_identities {n m : SemiSimplexCategory} (f : n ⟶ m)
    (hf : ¬ identities _ f) : n.len < m.len := by
  refine (len_le_of_hom f).lt_of_ne fun h ↦ hf ?_
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  dsimp at h
  subst h
  rw [eq_id_of_endo f]
  exact .mk _

/-- The Reedy structure making `SemiSimplexCategory` a direct category, with degree `len`. -/
def reedyStructure : ReedyStructure (identities SemiSimplexCategory) ⊤ ℕ where
  deg := len
  lt₁ _ hf hf' := absurd hf hf'
  lt₂ f _ hf' := len_lt_of_not_identities f hf'
  nonempty_unique _ := ⟨inferInstance⟩

end SemiSimplexCategory

