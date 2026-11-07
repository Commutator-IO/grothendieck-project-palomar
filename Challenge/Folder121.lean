module

public import Mathlib.Topology.Closure
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.WellFounded
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace Grothendieck.Folder121

open Set

variable {X : Type*} [TopologicalSpace X]

/-- `B` is rare in `Z`: no nonempty relatively open part of `Z` lies in `B`. -/
def Rare (B Z : Set X) : Prop := ∀ V, IsOpen V → V ∩ Z ⊆ B → V ∩ Z = ∅

/-- Conditions a) to e) of pages 3–5 on a family `F` of parts of `X`. -/
structure Tame (F : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F
  closure_mem : ∀ A ∈ F, closure A ∈ F
  dense_open : ∀ A ∈ F, ∃ G, IsOpen G ∧ G ∩ closure A ⊆ A ∧ closure A ⊆ closure (G ∩ closure A)
  dcc : ∀ A : ℕ → Set X, (∀ n, A n ∈ F ∧ IsClosed (A n)) →
    (∀ n, A (n + 1) ⊆ A n ∧ Rare (A (n + 1)) (A n)) → ∃ n, A n = ∅

variable {F : Set (Set X)}

/-- A finite cellular decomposition of `Z` (page 10): nonempty disjoint cells covering `Z`,
the closure of a cell a union of cells (1), distinct cells with distinct closures (2). -/
structure IsDecomp (Z : Set X) (P : Finset (Set X)) : Prop where
  nonempty : ∀ c ∈ P, c.Nonempty
  disjoint : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → Disjoint c d
  cover : ⋃ c ∈ P, c = Z
  frontier : ∀ c ∈ P, ∀ d ∈ P, (closure c ∩ d).Nonempty → d ⊆ closure c
  distinct : ∀ c ∈ P, ∀ d ∈ P, closure c = closure d → c = d

/-- Every member of `L` is a union of cells. -/
def Compat (L P : Finset (Set X)) : Prop := ∀ Y ∈ L, ∀ c ∈ P, c ⊆ Y ∨ Disjoint c Y

/-- An `F`-admissible decomposition of `Z` for which the members of `L` are unions of
cells. -/
def Good (F : Set (Set X)) (L : Finset (Set X)) (Z : Set X) (P : Finset (Set X)) : Prop :=
  IsDecomp Z P ∧ (∀ c ∈ P, c ∈ F) ∧ Compat L P

/-- `P` is coarser than `Q`: every cell of `Q` lies in a cell of `P`. -/
def Coarser (P Q : Finset (Set X)) : Prop := ∀ q ∈ Q, ∃ p ∈ P, q ⊆ p

/-- **Page 14.** Under a) to e), for every finite family `L ⊂ F` there is an `F`-admissible
cellular decomposition of `X` of which the members of `L` are unions of cells, and among them
one coarser than all the others. -/
theorem page14 (hF : Tame F) (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, Good F L univ P ∧ ∀ Q, Good F L univ Q → Coarser P Q := by
  sorry

end Grothendieck.Folder121
