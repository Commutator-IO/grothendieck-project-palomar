module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

@[expose] public section

open Polynomial

namespace Grothendieck.Folder63

/-- `ℤ[ζ]`, `ζ` a primitive cube root of unity. -/
abbrev R := AdjoinRoot (X ^ 2 + X + 1 : ℤ[X])

/-- `ζ`. -/
noncomputable abbrev ζ : R := AdjoinRoot.root _

/-- `P = (2, t)`. -/
noncomputable def P : Ideal R[X] := Ideal.span {C 2, X}

/-- The four values `0, 1, ζ, ζ²`. -/
noncomputable def α : Fin 4 → R := ![0, 1, ζ, ζ ^ 2]

/-- The four branches `t + 2α` of `V(c₄)` through `a`. -/
noncomputable def branch (i : Fin 4) : R[X] := X + 2 * C (α i)

/-- **The four tangents are pairwise distinct**: for `i ≠ j`, `a · branch i + b · branch j ∈ P²`
forces `a, b ∈ P`. -/
theorem tangents_distinct (i j : Fin 4) (hij : i ≠ j) (a b : R[X])
    (h : a * branch i + b * branch j ∈ P ^ 2) : a ∈ P ∧ b ∈ P := by
  sorry

end Grothendieck.Folder63
