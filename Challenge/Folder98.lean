module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Multiset.Bind
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Algebra.Group.Action.Sum

@[expose] public section

namespace Grothendieck.Folder98

variable {X Y Z : Type*}

section ExampleIII

open Topology

variable {Γ : Type*} [Group Γ] {X : Type*} [MulAction Γ X]
  {E F : Type*} [MulAction Γ E] [MulAction Γ F]

variable (Γ X) in
/-- `Φ(E) = X ×^Γ E`, the contracted product. -/
abbrev Phi (E : Type*) [MulAction Γ E] := Quotient (MulAction.orbitRel Γ (X × E))

variable (Γ X) in
/-- `Φ(f) : X ×^Γ E → X ×^Γ F` for an equivariant `f : E → F`. -/
def Phi.map (f : E → F) (hf : ∀ (g : Γ) e, f (g • e) = g • f e) : Phi Γ X E → Phi Γ X F :=
  Quotient.map (Prod.map id f) fun _ b ⟨g, h⟩ => ⟨g, h ▸ Prod.ext rfl (hf g b.2).symm⟩

section Topology

variable [TopologicalSpace X] [ContinuousConstSMul Γ X] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace F] [DiscreteTopology F]

/-- Example III: for `Γ` acting on `X` with every point having a neighbourhood disjoint from its
translates, `Φ` takes every equivariant map of discrete `Γ`-sets to a covering map; by
`hasDeg_phi`, one with `r` sheets when the map has degree `r`. -/
theorem isCoveringMap_phi
    (hdisj : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : Γ, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) : IsCoveringMap (Phi.map Γ X f hf) := by
  sorry

end Topology

end ExampleIII

end Grothendieck.Folder98
