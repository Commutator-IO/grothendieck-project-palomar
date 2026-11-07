module

public import Mathlib
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin

@[expose] public section


/-!
# Folder 89: the « fundamental relation » of the 3-3 sets, pages 15–18

On a free module of rank two, with `u ∧ v` the determinant of the pair, the reading of folder 89
states, for `u` and `v` spanning (here: `u ∧ v` a unit),

  `u ∧ v = v ∧ w = w ∧ u  ⟺  u + v + w = 0`,

and notes that the statement holds over any commutative ring, the page saying only « on vérifie de
suite ». The proof below is the edition's: Cramer's identity
`(v ∧ w) • u + (w ∧ u) • v + (u ∧ v) • w = 0` gives `d • (u + v + w) = 0` when all three wedges
equal `d`, and `d` is a unit.
-/

namespace Grothendieck.Folder89

variable {R : Type*} [CommRing R]

/-- The wedge `u ∧ v` of two vectors of `R²`: the determinant of the pair. -/
def wedge (u v : Fin 2 → R) : R := u 0 * v 1 - u 1 * v 0

/-- Cramer's identity in rank two, coordinate by coordinate. -/
theorem cramer (u v w : Fin 2 → R) (i : Fin 2) :
    wedge v w * u i + wedge w u * v i + wedge u v * w i = 0 := by
  fin_cases i <;> simp [wedge] <;> ring

/-- Folder 89, pages 15–18: for `u ∧ v` a unit, `u ∧ v = v ∧ w = w ∧ u` exactly when
`u + v + w = 0`, over any commutative ring. -/
theorem fundamental_relation (u v w : Fin 2 → R) (hd : IsUnit (wedge u v)) :
    (wedge u v = wedge v w ∧ wedge v w = wedge w u) ↔ u + v + w = 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    funext i
    have hc := cramer u v w i
    rw [← h₁, ← h₂, ← h₁] at hc
    have : wedge u v * (u i + v i + w i) = 0 := by linear_combination hc
    simpa using (hd.mul_right_eq_zero).1 this
  · intro h
    have hw : w = -(u + v) := eq_neg_of_add_eq_zero_right h
    subst hw
    constructor <;> simp [wedge] <;> ring

end Grothendieck.Folder89
