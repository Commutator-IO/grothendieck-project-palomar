module

public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

public section

/-!
# Advertised statement: the bigon-free dichotomy for combinatorial pseudoline arrangements

A combinatorial arrangement of pseudolines in the real projective plane is a generalised map
with flags labelled by lines (`PseudolineMap`). If no line carries fewer than three vertices
(`BigonFree`), the arrangement is four lines in general position (`IsII4`) or contains five
lines in general position, a pencil of three and a pencil of two in which none of these five lines joins the two centres, or the complete quadrangle.
-/

namespace Grothendieck.Folder80Maps2

section Core

variable {P L : Type*} (on : P → L → Prop)

/-- Three lines are concurrent. -/
def C (a b c : L) : Prop := ∃ p, on p a ∧ on p b ∧ on p c

/-- Four lines in general position: distinct, no three concurrent. -/
def GP4 (a b c d : L) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ¬C on a b c ∧ ¬C on a b d ∧ ¬C on a c d ∧ ¬C on b c d

/-- Five lines in general position: distinct, no three concurrent. -/
def GP5 (a b c d e : L) : Prop :=
  GP4 on a b c d ∧ a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e ∧
    ¬C on a b e ∧ ¬C on a c e ∧ ¬C on a d e ∧ ¬C on b c e ∧ ¬C on b d e ∧ ¬C on c d e

/-- Every line carries at least three vertices. -/
def BigonFree : Prop := ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- `II_4`: the arrangement is four lines in general position. -/
def IsII4 : Prop := ∃ a b c d, GP4 on a b c d ∧ ∀ m, m = a ∨ m = b ∨ m = c ∨ m = d

/-- `II_5`: five lines in general position. -/
def HasII5 : Prop := ∃ a b c d e, GP5 on a b c d e

/-- `II′_{3,2}`: `a, b, c` through `p`, `d, e` not through `p`, and their meeting point on none
of `a, b, c` (so, among these five lines, it is the only concurrent triple, and none of the five joins
the two centres; another line of the arrangement may join them). -/
def HasII32 : Prop :=
  ∃ a b c d e : L, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ ∃ p, on p a ∧ on p b ∧ on p c ∧ ¬on p d ∧
    ¬on p e ∧ ∀ q, on q d → on q e → ¬on q a ∧ ¬on q b ∧ ¬on q c

/-- No line of the arrangement passes through `p`, `q` and `r`. -/
def NC (p q r : P) : Prop := ∀ m, on p m → on q m → ¬on r m

/-- Some line of the arrangement passes through `p` and `q`. -/
def J (p q : P) : Prop := ∃ m, on p m ∧ on q m

/-- `III_6`, the complete quadrangle: four points, no three on a line, pairwise joined. -/
def HasIII6 : Prop :=
  ∃ p q r s : P, J on p q ∧ J on p r ∧ J on p s ∧ J on q r ∧ J on q s ∧ J on r s ∧
    NC on p q r ∧ NC on p q s ∧ NC on p r s ∧ NC on q r s

end Core

section Maps

open Relation


/-- A generalised map (a combinatorial map of a possibly non-orientable surface): flags with
three fixed-point-free involutions, `a0` and `a2` commuting with `a0 a2` fixed-point-free. -/
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d


namespace GMap

variable {D : Type*} (M : GMap D)

/-- Vertices are the classes of `⟨a1, a2⟩`. -/
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x
/-- Edges are the classes of `⟨a0, a2⟩`. -/
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x
/-- Faces are the classes of `⟨a0, a1⟩`. -/
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x

/-- The vertex of a flag. -/
def vtx (d : D) : M.Vtx := Quot.mk _ d
/-- The edge of a flag. -/
def edge (d : D) : M.Edge := Quot.mk _ d
/-- The face of a flag. -/
def face (d : D) : M.Face := Quot.mk _ d


/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face


end GMap

open GMap

/-- A combinatorial pseudoline arrangement (page 60): a generalised map with flags labelled by
lines, constant on edges; a line through a vertex has there the four flags of two edge-ends
(it passes once); each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; the surface is a projective plane, `χ = 1`. -/
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1

namespace PseudolineMap

variable {D L : Type*} (X : PseudolineMap D L)

/-- The line `l` passes through the vertex `v`. -/
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l

variable {X}

-- Finitely many flags: the Euler characteristic `χ = 1` is meaningful for finite maps.
variable [Fintype D]


/-- **The page's boxed statement** (pages 20, 24): every bigon-free combinatorial arrangement of
pseudolines in the real projective plane is `II_4` or contains `II_5`, `II′_{3,2}` or
`III_6`. -/
theorem map_dichotomy (hbf : BigonFree X.On) :
    IsII4 X.On ∨ HasII5 X.On ∨ HasII32 X.On ∨ HasIII6 X.On := by
  sorry

end PseudolineMap

end Maps

end Grothendieck.Folder80Maps2
