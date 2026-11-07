module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Grothendieck.Folder123Kostant

/-- `card(W)`, `h`, `z` for a simple type: `(|W|, h, z)`. -/
def dataA (n : ℕ) : ℕ × ℕ × ℕ := ((n + 1).factorial, n + 1, n + 1)

def dataB (n : ℕ) : ℕ × ℕ × ℕ := (2 ^ n * n.factorial, 2 * n, 2)

def dataG2 : ℕ × ℕ × ℕ := (12, 6, 1)

/-- The announced number of classes. -/
def number (d : ℕ × ℕ × ℕ) : ℕ := d.1 ^ 2 / (d.2.1 * d.2.2 * Nat.totient d.2.1)

/-- The hand checks of the reading: `A₁`, `A₂`, `B₂`, `G₂` give 1, 2, 4, 12. -/
theorem small_cases :
    number (dataA 1) = 1 ∧ number (dataA 2) = 2 ∧ number (dataB 2) = 4 ∧ number dataG2 = 12 := by
  sorry

end Grothendieck.Folder123Kostant
