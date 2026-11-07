module

public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

open Complex Polynomial

open scoped Pointwise

namespace Grothendieck.Folder13

/-- **Grothendieck, page 47, the Tate case** (« c'est une puissance de Tate, et ça marche »;
forme reconstituée par l'édition). For the Tate motive `ℚ(n)`, the rational numbers lying in
the de Rham line `(2πi)ⁿ ℚ̄` are all of `ℚ` when `n = 0` and only `0` otherwise, which is
`V^G` for the weight-`n` character of `𝔾_m`. Assumes the transcendence of `π` (Lindemann),
not in Mathlib. -/
theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} := by
  sorry

end Grothendieck.Folder13
