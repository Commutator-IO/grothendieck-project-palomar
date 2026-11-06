module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.VecNotation

public section


/-!
# Folder 80, page 24: the « crucial » arrangements and a counterexample to the Théorème

The modernised reading `transcripts/80/80.modern.tex` (§ III, « Les arrangements
cruciaux ») lists types of arrangements of pseudolines: `I_N`, `I_{p,q}`, `II′_{p,q}` (two
pencils), `II_4`, `II_5` (four, five lines in general position), `III_6` (the complete
quadrangle: six lines, four triple points), `IV_7` (a complete quadrilateral and its three
diagonals). Page 24:

> Théorème : supposons qu'il n'existe pas deux sommets tels que les ps. droites passent par
> l'un d'eux […]. Supposons de plus que K ne contienne pas de sous-arrangement du type II_5 ;
> elle est de l'un des types suivants : III_6, IV_7.

This is finding `80-crucial-arrangements-theorem`. A counterexample made of straight lines of
the real projective plane is enough; the lines are written as integer triples `(u₀, u₁, u₂)`
(the line `u₀x + u₁y + u₂z = 0`), and three lines are concurrent iff the determinant of their
triples vanishes (`det3_eq_det`).

* `six`: the sides `AB`, `BC`, `CA` of the triangle `A = (0, 0)`, `B = (1, 0)`, `C = (0, 1)`,
  and the lines `a : y = 2x` through `A`, `b : y = 3x − 3` through `B`, `c : y = 5x + 1`
  through `C`.
* `six_concurrent`: the concurrent triples are exactly `{AB, CA, a}`, `{AB, BC, b}`,
  `{CA, BC, c}` (three triple points, no two lines equal);
* `six_not_two_pencils`: no two vertices `P`, `Q` have every line through `P` or `Q`;
* `six_no_II5`: every five of the six lines contain a concurrent triple, so there is no `II_5`;
* `six_not_III6`: there are three triple points and not four, so the arrangement is not the
  complete quadrangle `III_6`; it has six lines, so it is not `IV_7` either;
* `six_has_II32`: the five lines `AB, CA, a, b, c` form a `II′_{3,2}` (one triple point, the
  other intersections double).
* `seven_has_II32`: the reading's correction of the parenthesis of page 24 — in `IV_7`
  (`AB, BC, CD, DA, AC, BD, EF` for the square `A, B, C, D`, `E, F` at infinity) the five lines
  `AB, AD, AC, BD, EF` have a single triple point.

**What the formalisation finds.** The Théorème fails as written, already for straight lines:
the counterexample contains `II′_{3,2}`, so the version with that extra hypothesis
(`II′_{3,2}` and `II_5` excluded, conclusion `II_4` or `III_6`) is untouched. Not
formalised: pseudolines in general, bigons, and that version itself.
-/

namespace Grothendieck.Folder80

/-- The determinant of three integer triples. -/
def det3 (u v w : Fin 3 → ℤ) : ℤ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

theorem det3_eq_det (u v w : Fin 3 → ℤ) : det3 u v w = Matrix.det (Matrix.of ![u, v, w]) := by
  rw [Matrix.det_fin_three]
  simp [det3]
  ring

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

/-- The concurrent triples (`i < j < k`) are `{AB, CA, a}`, `{AB, BC, b}`, `{BC, CA, c}`. -/
theorem six_concurrent :
    (Finset.univ.filter fun t : Fin 6 × Fin 6 × Fin 6 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Concurrent six t.1 t.2.1 t.2.2) =
      {(0, 2, 3), (0, 1, 4), (1, 2, 5)} := by
  decide

/-- The six lines are pairwise distinct: no two triples are proportional. -/
theorem six_distinct (i j : Fin 6) (h : i ≠ j) :
    ∃ k : Fin 6, ¬ Concurrent six i j k := by
  revert i j; decide

/-- **Not covered by two pencils**: no two vertices have every line through one of them. -/
theorem six_not_two_pencils :
    ¬ ∃ i j k l : Fin 6, i ≠ j ∧ k ≠ l ∧ ∀ m, Through six m i j ∨ Through six m k l := by
  decide

/-- **No `II_5`**: any five of the lines contain a concurrent triple. -/
theorem six_no_II5 :
    ∀ S : Finset (Fin 6), S.card = 5 →
      ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i < j ∧ j < k ∧ Concurrent six i j k := by
  decide

/-- **Not `III_6`**: three concurrent triples, where the complete quadrangle has four. -/
theorem six_not_III6 :
    (Finset.univ.filter fun t : Fin 6 × Fin 6 × Fin 6 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Concurrent six t.1 t.2.1 t.2.2).card = 3 := by
  rw [six_concurrent]; decide

/-- The five lines `AB, CA, a, b, c` form a `II′_{3,2}`: their only concurrent triple is
`{AB, CA, a}`. -/
theorem six_has_II32 :
    (Finset.univ.filter fun t : Fin 6 × Fin 6 × Fin 6 =>
        t.1 ∈ ({0, 2, 3, 4, 5} : Finset (Fin 6)) ∧ t.2.1 ∈ ({0, 2, 3, 4, 5} : Finset (Fin 6)) ∧
        t.2.2 ∈ ({0, 2, 3, 4, 5} : Finset (Fin 6)) ∧
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Concurrent six t.1 t.2.1 t.2.2) = {(0, 2, 3)} := by
  decide

/-- `IV_7`: `AB, BC, CD, DA, AC, BD, EF` for the square `A = (0, 0)`, `B = (1, 0)`,
`C = (1, 1)`, `D = (0, 1)`, with `E = AB ∩ CD` and `F = AD ∩ BC` at infinity. -/
def seven : Fin 7 → Fin 3 → ℤ :=
  ![![0, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, 0], ![1, -1, 0], ![1, 1, -1], ![0, 0, 1]]

/-- `seven` is a `IV_7`: six triple points, the vertices of the quadrilateral. -/
theorem seven_concurrent :
    (Finset.univ.filter fun t : Fin 7 × Fin 7 × Fin 7 =>
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Concurrent seven t.1 t.2.1 t.2.2).card = 6 := by
  decide

/-- **The reading's correction**: `IV_7` contains a `II′_{3,2}`, the lines `AB, DA, AC, BD, EF`,
whose only concurrent triple is `{AB, DA, AC}`. -/
theorem seven_has_II32 :
    (Finset.univ.filter fun t : Fin 7 × Fin 7 × Fin 7 =>
        t.1 ∈ ({0, 3, 4, 5, 6} : Finset (Fin 7)) ∧ t.2.1 ∈ ({0, 3, 4, 5, 6} : Finset (Fin 7)) ∧
        t.2.2 ∈ ({0, 3, 4, 5, 6} : Finset (Fin 7)) ∧
        t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Concurrent seven t.1 t.2.1 t.2.2) = {(0, 3, 4)} := by
  decide

end Grothendieck.Folder80
