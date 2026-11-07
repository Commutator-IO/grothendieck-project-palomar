module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder80Maps3

open Relation

/-- A generalised map: flags with three fixed-point-free involutions, `a0` and `a2` commuting
with `a0 a2` fixed-point-free. -/
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

/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face

variable {M}

end GMap

open GMap

/-- Every line carries at least three vertices. -/
def BigonFree {P L : Type*} (on : P → L → Prop) : Prop :=
  ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- A combinatorial pseudoline arrangement (page 60), as in `Folder80Maps2`: a generalised map
with flags labelled by lines, constant on edges; a line through a vertex has there the four
flags of two edge-ends; each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; `χ = 1`. -/
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

variable [Fintype D]

section Chains

open Matrix

variable (X) in
/-- The vertex `v` is an end of the edge `e`. -/
def Inc (v : X.M.Vtx) (e : X.M.Edge) : Prop := ∃ d, X.M.vtx d = v ∧ X.M.edge d = e

variable (X) in
/-- The line of an edge. -/
def lineE : X.M.Edge → L :=
  Quot.lift X.line fun x _ h => h.elim (fun h => h ▸ (X.line_a0 x).symm) fun h =>
    h ▸ (X.line_a2 x).symm

end Chains

variable (X) in
/-- The rotation `φ = a2 a1` around a vertex: from an edge-end to the next one. -/
def phi : Equiv.Perm D :=
  Function.Involutive.toPerm X.M.a2 X.M.a2_a2 * Function.Involutive.toPerm X.M.a1 X.M.a1_a1

open Classical in
variable (X) in
/-- The number `ν(v)` of lines through a vertex. -/
noncomputable def nu (v : X.M.Vtx) : ℕ :=
  ((Finset.univ.filter fun d => X.M.vtx d = v).image X.line).card

variable (X) in
/-- **Going straight** (page 60; (22) of page 41): half a turn around a vertex of `ν` lines,
`ν` edge-ends further, one finds the same line. -/
def Straight : Prop := ∀ d, X.line ((X.phi ^ X.nu (X.M.vtx d)) d) = X.line d

section Lift

variable (X) in
/-- `e1, e, e2` are three consecutive sides of a face: the corner `(e1, e)` at one end of `e`
continued along `e` to the corner `(e, e2)` on the same side. These paths are the generalised
rotation system (19)–(21) of page 41. -/
def Path3 (e1 e e2 : X.M.Edge) : Prop :=
  ∃ d, X.M.edge (X.M.a1 d) = e1 ∧ X.M.edge d = e ∧ X.M.edge (X.M.a1 (X.M.a0 d)) = e2

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

variable (X X') in
/-- An isomorphism of the skeletons decomposed into lines: bijections of vertices, edges and
lines preserving incidence and the line of each edge (the arrangements of dimension `1` of
page 40). -/
structure SkelIso where
  fV : X.M.Vtx ≃ X'.M.Vtx
  fE : X.M.Edge ≃ X'.M.Edge
  fL : L ≃ L'
  inc : ∀ v e, X.Inc v e ↔ X'.Inc (fV v) (fE e)
  line : ∀ e, X'.lineE (fE e) = fL (X.lineE e)

/-- The inverse isomorphism of skeletons. -/
def SkelIso.symm (f : SkelIso X X') : SkelIso X' X where
  fV := f.fV.symm
  fE := f.fE.symm
  fL := f.fL.symm
  inc v e := by rw [f.inc]; simp
  line e := by rw [Equiv.eq_symm_apply, ← f.line]; simp

/-- **Fullness reduces to face paths.** An isomorphism of decomposed skeletons of two bigon-free
arrangements comes from an isomorphism of the arrangements (a bijection of flags commuting with
`a0, a1, a2`) iff it preserves the three-edge face paths in both directions; the isomorphism is
then unique (`faithful`). -/
theorem lift_iff (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (f : SkelIso X X') :
    (∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ↔
    ∀ e1 e e2, X.Path3 e1 e e2 ↔ X'.Path3 (f.fE e1) (f.fE e) (f.fE e2) := by
  sorry

end Lift

end PseudolineMap

end Grothendieck.Folder80Maps3
