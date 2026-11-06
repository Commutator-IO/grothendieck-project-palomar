module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Folder 123: the number of Kostant rigidifications, `card(W)² / (h z φ(h))`, in small rank

For `G` simple adjoint, the folder announces that the conjugacy classes of quadruples `(T, B, T', B')`
(`T`, `T'` maximal tori « en apposition », `B ⊃ T`, `B' ⊃ T'` Borel subgroups) number
`card(W)² / (h z φ(h))`, with `W` the Weyl group, `h` the Coxeter number, `z` the order of the
centre of the simply connected group and `φ` Euler's function. The folder proves neither the count
nor the free action behind it; the reading checks by hand that the numbers are integers for `A₁`,
`A₂`, `B₂`, `G₂` (1, 2, 4, 12). This file checks that the formula gives an integer, and its value,
for every simple type of rank at most 8 and for the exceptional types (#91, nv:87). It checks the
arithmetic of the announced number, not the geometry.
-/

namespace Grothendieck.Folder123Kostant

/-- `card(W)`, `h`, `z` for a simple type: `(|W|, h, z)`. -/
def dataA (n : ℕ) : ℕ × ℕ × ℕ := ((n + 1).factorial, n + 1, n + 1)
def dataB (n : ℕ) : ℕ × ℕ × ℕ := (2 ^ n * n.factorial, 2 * n, 2)
def dataC (n : ℕ) : ℕ × ℕ × ℕ := (2 ^ n * n.factorial, 2 * n, 2)
def dataD (n : ℕ) : ℕ × ℕ × ℕ := (2 ^ (n - 1) * n.factorial, 2 * n - 2, 4)
def dataE6 : ℕ × ℕ × ℕ := (51840, 12, 3)
def dataE7 : ℕ × ℕ × ℕ := (2903040, 18, 2)
def dataE8 : ℕ × ℕ × ℕ := (696729600, 30, 1)
def dataF4 : ℕ × ℕ × ℕ := (1152, 12, 1)
def dataG2 : ℕ × ℕ × ℕ := (12, 6, 1)

/-- The announced denominator `h z φ(h)` divides `card(W)²` (as a remainder, so that it decides). -/
abbrev integral (d : ℕ × ℕ × ℕ) : Prop := d.1 ^ 2 % (d.2.1 * d.2.2 * Nat.totient d.2.1) = 0

/-- The announced number of classes. -/
def number (d : ℕ × ℕ × ℕ) : ℕ := d.1 ^ 2 / (d.2.1 * d.2.2 * Nat.totient d.2.1)

/-- The hand checks of the reading: `A₁`, `A₂`, `B₂`, `G₂` give 1, 2, 4, 12. -/
theorem small_cases :
    number (dataA 1) = 1 ∧ number (dataA 2) = 2 ∧ number (dataB 2) = 4 ∧ number dataG2 = 12 := by
  decide

theorem integral_A : ∀ n ∈ Finset.Icc 1 8, integral (dataA n) := by decide
theorem integral_B : ∀ n ∈ Finset.Icc 2 8, integral (dataB n) := by decide
theorem integral_C : ∀ n ∈ Finset.Icc 3 8, integral (dataC n) := by decide
theorem integral_D : ∀ n ∈ Finset.Icc 4 8, integral (dataD n) := by decide

theorem integral_exceptional :
    integral dataE6 ∧ integral dataE7 ∧ integral dataE8 ∧ integral dataF4 ∧ integral dataG2 := by
  decide

end Grothendieck.Folder123Kostant
