module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.Group

@[expose] public section

namespace Grothendieck.Folder69

open Equiv

/-- The fifteen pairs `i < j` of `{0, …, 5}`, in lexicographic order. -/
def pairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The pair of `c_{ij}`. -/
def cp (v : Fin 27) : ℕ × ℕ := pairs.getD (v.val - 12) (0, 0)

/-- Do two of the twenty-seven lines meet? -/
def meets (u v : Fin 27) : Bool :=
  if u.val < 12 ∧ v.val < 12 then
    (u.val < 6 ∧ 6 ≤ v.val ∧ u.val + 6 ≠ v.val) || (v.val < 6 ∧ 6 ≤ u.val ∧ v.val + 6 ≠ u.val)
  else if u.val < 12 then (cp v).1 = u.val % 6 || (cp v).2 = u.val % 6
  else if v.val < 12 then (cp u).1 = v.val % 6 || (cp u).2 = v.val % 6
  else (cp u).1 ≠ (cp v).1 ∧ (cp u).1 ≠ (cp v).2 ∧ (cp u).2 ≠ (cp v).1 ∧ (cp u).2 ≠ (cp v).2

/-- The graph `C` of the twenty-seven lines. -/
def C : SimpleGraph (Fin 27) where
  Adj u v := meets u v = true
  symm := ⟨fun u v h =>
    ((show ∀ u v : Fin 27, meets u v = meets v u by decide +kernel) u v).symm.trans h⟩
  loopless := ⟨fun u h => by
    rw [(show ∀ u : Fin 27, meets u u = false by decide +kernel) u] at h
    exact Bool.false_ne_true h⟩

instance : DecidableRel C.Adj := fun u v => inferInstanceAs (Decidable (meets u v = true))

/-- The marked triangle `t = {a₀, b₁, c₀₁}`. -/
def t : Finset (Fin 27) := {0, 7, 12}

/-- The same count for the graph automorphisms `C ≃g C` that preserve `t`. -/
theorem card_aut : Nat.card {f : C ≃g C // ∀ v, f v ∈ t ↔ v ∈ t} = 1152 := by
  sorry

end Grothendieck.Folder69
