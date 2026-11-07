module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace Grothendieck.Folder158

universe u

/-- **Pseudo-cofiltrant** (the reading's footnote, from manuscript p. 55):
`∀ u, v`, `∃ u', v'` with `u u' = v v'` — any two principal right ideals meet. -/
def PseudoCofiltrant (M : Type u) [Monoid M] : Prop :=
  ∀ u v : M, ∃ u' v' : M, u * u' = v * v'

/-- **Cofiltrant**: pseudo-cofiltrant, and any two parallel arrows (here, any
two elements) are equalised further on: `∀ u, v`, `∃ w` with `u w = v w`. -/
def Cofiltrant (M : Type u) [Monoid M] : Prop :=
  PseudoCofiltrant M ∧ ∀ u v : M, ∃ w : M, u * w = v * w

/-- **Groupe enveloppant trivial**: every monoid morphism from `M` to a group is
trivial (the universal property of the group completion, for groups in `M`'s
universe, where the group completion lives). -/
def GroupeEnveloppantTrivial (M : Type u) [Monoid M] : Prop :=
  ∀ (G : Type u) [Group G] (f : M →* G), f = 1

variable {M : Type u} [Monoid M]

/-- **Proposition 1.** Let `M` be a finite pseudo-cofiltering monoid with
trivial group completion. Then there is `p ∈ M` with `u p = p` for every
`u ∈ M`; in particular `p² = p`, and `M` is cofiltering. -/
theorem proposition1 [Finite M] (hpc : PseudoCofiltrant M)
    (hG : GroupeEnveloppantTrivial M) :
    ∃ p : M, (∀ u : M, u * p = p) ∧ p * p = p ∧ Cofiltrant M := by
  sorry

open CategoryTheory

universe v w

end Grothendieck.Folder158
