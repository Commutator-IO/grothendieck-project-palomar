module

public import Mathlib.Tactic.NormNum
public import Mathlib.Data.List.Basic

@[expose] public section

namespace Grothendieck.Folder148Chart

/-- The nine types of page 30, by level: the order of `G` for each. `I₁₀` has `G = 𝔻₅` (order 10),
`I₆` has `𝔖₃`, `I₄` has `ℤ/4`; the others have `ℤ/2` or `1`. -/
def orders : List ℕ := [10, 6, 4, 2, 2, 1, 2, 1, 2]

/-- The number of structures of each type, `120 / |G|`. -/
def counts : List ℕ := orders.map (120 / ·)

/-- Level by level, 62, 240 and 240 structures; 542 vertices in all. -/
theorem vertices :
    (counts.take 3).sum = 62 ∧ ((counts.drop 3).take 3).sum = 240 ∧ (counts.drop 6).sum = 240 ∧
      counts.sum = 542 := by
  sorry

end Grothendieck.Folder148Chart
