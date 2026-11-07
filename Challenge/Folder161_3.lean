module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Sober

@[expose] public section

namespace Grothendieck.Folder161_3

open TopologicalSpace Set

/-- The page's hypothesis: every nonempty locally closed `Z ⊆ X` has a point `x`
with a quasi-compact neighbourhood `T` in `Z`, i.e. `O ∩ Z ⊆ T ⊆ Z` for an
open `O ∋ x`. -/
def HypG (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Z : Set X, IsLocallyClosed Z → Z.Nonempty →
    ∃ x ∈ Z, ∃ T ⊆ Z, IsCompact T ∧ ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ∩ Z ⊆ T

/-- A set of pairs of opens, stable under shrinking and under arbitrary unions in
each variable: an element of the frame coproduct of `Opens X` and `Opens Y`, the
« S » of the page. -/
@[ext]
structure CIdeal (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  carrier : Set (Opens X × Opens Y)
  mono : ∀ {U U' V V'}, (U, V) ∈ carrier → U' ≤ U → V' ≤ V → (U', V') ∈ carrier
  sSup_left : ∀ (s : Set (Opens X)) V,
    (∀ U ∈ s, (U, V) ∈ carrier) → (sSup s, V) ∈ carrier
  sSup_right : ∀ U (s : Set (Opens Y)),
    (∀ V ∈ s, (U, V) ∈ carrier) → (U, sSup s) ∈ carrier

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pages 10–11: under `HypG X`, a `CIdeal` contains every rectangle covered by
its own rectangles. -/
theorem covering (hG : HypG X) (S : CIdeal X Y) (U : Opens X) (V : Opens Y)
    (h : (U : Set X) ×ˢ (V : Set Y) ⊆ ⋃ p ∈ S.carrier, (p.1 : Set X) ×ˢ (p.2 : Set Y)) :
    (U, V) ∈ S.carrier := by
  sorry

open Function (eval update update_of_ne update_self)

end Grothendieck.Folder161_3
