module

public import Mathlib.Tactic.NormNum
public import Mathlib.Data.List.Basic

public section


/-!
# Folder 148, pages 30–32: the counts of the chart of special structures on five points

Page 30 tabulates nine types of « special » structures on a five-point set `K`, on the three levels
of the strata of `M̄₀,₅`; the number of structures of a type is `120 / |G|`, with `G` the group of
holomorphic automorphisms of the structure (`120 = |𝔖₅|`). Page 32 counts the arrows between them,
fourteen types in three groups. The folder states 542 vertices and 1620 arrows; this file checks
these counts from the orders of the groups and the arrow numbers as the reading tabulates them. It
checks the arithmetic of the chart, not the classification of the structures (#91, nv:97).
-/

namespace Grothendieck.Folder148Chart

/-- The nine types of page 30, by level: the order of `G` for each. `I₁₀` has `G = 𝔻₅` (order 10),
`I₆` has `𝔖₃`, `I₄` has `ℤ/4`; the others have `ℤ/2` or `1`. -/
def orders : List ℕ := [10, 6, 4, 2, 2, 1, 2, 1, 2]

/-- The number of structures of each type, `120 / |G|`. -/
def counts : List ℕ := orders.map (120 / ·)

theorem counts_eq : counts = [12, 20, 30, 60, 60, 120, 60, 120, 60] := by decide

/-- Level by level, 62, 240 and 240 structures; 542 vertices in all. -/
theorem vertices :
    (counts.take 3).sum = 62 ∧ ((counts.drop 3).take 3).sum = 240 ∧ (counts.drop 6).sum = 240 ∧
      counts.sum = 542 := by decide

/-- The arrows of page 32, in the reading's three groups (each type counted once, by its sources). -/
def arrows : List (List ℕ) :=
  [[60, 120], [60, 120, 60, 60, 120], [120, 120, 120, 120, 360, 120, 60]]

theorem arrows_eq : arrows.map List.sum = [180, 420, 1020] ∧ (arrows.map List.sum).sum = 1620 ∧
    (arrows.map List.length).sum = 14 := by decide

end Grothendieck.Folder148Chart
