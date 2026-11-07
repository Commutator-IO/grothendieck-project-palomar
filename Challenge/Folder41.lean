module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Sober

@[expose] public section

namespace Grothendieck.Folder41

open Topology

section Topologie

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `φ(y)` is the generic point of the (irreducible, non-empty) fibre `f⁻¹(y)`:
it lies over `y` and specialises to every point over `y`. -/
def SectionGenerique (f : X → Y) (φ : Y → X) : Prop :=
  ∀ y, f (φ y) = y ∧ ∀ x, f x = y → φ y ⤳ x

variable {f : X → Y} {φ : Y → X} (hφ : SectionGenerique f φ)

include hφ

end Topologie

section Schemas

open AlgebraicGeometry

/-- **Proposition 1.** For a morphism of schemes locally of finite presentation
whose fibres are irreducible and non-empty with generic points `φ(y)`, the four
conditions (i), (ii), (iii), (iii bis) are equivalent. -/
theorem proposition1 {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (φ : Y → X)
    (hφ : SectionGenerique f φ) :
    List.TFAE [Continuous φ, IsOpenMap f, ∀ y y', y' ⤳ y → φ y' ⤳ φ y, GeneralizingMap f] := by
  sorry

end Schemas

end Grothendieck.Folder41
