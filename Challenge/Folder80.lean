module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Grothendieck.Folder80

/-- The determinant of three integer triples. -/
def det3 (u v w : Fin 3 → ℤ) : ℤ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Three lines (indices into an arrangement) are concurrent. -/
def Concurrent {n : ℕ} (L : Fin n → Fin 3 → ℤ) (i j k : Fin n) : Prop := det3 (L i) (L j) (L k) = 0

instance {n : ℕ} (L : Fin n → Fin 3 → ℤ) (i j k : Fin n) : Decidable (Concurrent L i j k) :=
  inferInstanceAs (Decidable (_ = _))

/-- Line `m` passes through the vertex `L i ∩ L j`. -/
def Through {n : ℕ} (L : Fin n → Fin 3 → ℤ) (m i j : Fin n) : Prop :=
  m = i ∨ m = j ∨ Concurrent L m i j

instance {n : ℕ} (L : Fin n → Fin 3 → ℤ) (m i j : Fin n) : Decidable (Through L m i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The counterexample: `AB, BC, CA, a, b, c` (indices `0, …, 5`). -/
def six : Fin 6 → Fin 3 → ℤ :=
  ![![0, 1, 0], ![1, 1, -1], ![1, 0, 0], ![2, -1, 0], ![3, -1, -3], ![5, -1, 1]]

/-- **Not covered by two pencils**: no two vertices have every line through one of them. -/
theorem six_not_two_pencils :
    ¬ ∃ i j k l : Fin 6, i ≠ j ∧ k ≠ l ∧ ∀ m, Through six m i j ∨ Through six m k l := by
  sorry

end Grothendieck.Folder80
