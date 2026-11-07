module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace Grothendieck.Folder89

variable {R : Type*} [CommRing R]

/-- The wedge `u ∧ v` of two vectors of `R²`: the determinant of the pair. -/
def wedge (u v : Fin 2 → R) : R := u 0 * v 1 - u 1 * v 0

/-- Folder 89, pages 15–18: for `u ∧ v` a unit, `u ∧ v = v ∧ w = w ∧ u` exactly when
`u + v + w = 0`, over any commutative ring. -/
theorem fundamental_relation (u v w : Fin 2 → R) (hd : IsUnit (wedge u v)) :
    (wedge u v = wedge v w ∧ wedge v w = wedge w u) ↔ u + v + w = 0 := by
  sorry

end Grothendieck.Folder89
