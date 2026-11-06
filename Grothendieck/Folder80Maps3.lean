module

public import Mathlib

@[expose] public section


/-!
# Folder 80, pages 39–54: the skeleton of a bigon-free arrangement, in combinatorial maps

Finding `80-skeleton-full-faithfulness`. Page 54 (« En résumé »):

> Le foncteur canonique du groupoïde des arrangements de pseudo-droites sans bigone vers celui
> des arrangements de dimension 1 de pseudo-droites sans bigone est pleinement fidèle.

**Model.** As in `Folder80Maps2`, an arrangement is a generalised map (flags, three involutions
`a0, a1, a2`) of Euler characteristic `1` whose flags are labelled by lines (page 60), and it is
*bigon-free* when every line carries at least three vertices. Page 60's « aller tout droit » is
the extra hypothesis `Straight`: with `φ = a2 a1` the rotation around a vertex of `ν` lines,
`φ^ν` returns to the same line. The arrangement of dimension `1` (page 40) is the skeleton —
vertices, edges, incidence — with the line of each edge; `SkelIso` is an isomorphism of these.

**What is proved.**
* `faithful`: two isomorphisms of arrangements inducing the same maps on vertices and edges are
  equal — the functor is faithful.
* `lift`, `lift_iff`: page 41's « théorème général des cartes ». A skeleton isomorphism comes
  from an isomorphism of arrangements iff it preserves the three-edge face paths `Path3`
  (a corner continued along an edge to the next corner: the rotation system (19)–(21)).
  Fullness is thus reduced to the statement that these paths are read on the skeleton.
* `finrank_Z1_le`: mod 2, the cycles `Z₁` of the skeleton exceed the boundaries `B₁` of unions
  of faces by at most one dimension — the relation `c₂ = c(K)` of page 42, from `χ = 1`.
* `rot_card`: going straight, half a turn around a vertex meets every other line exactly once.
* `parity`: a closed line crosses the boundary of a union of faces an even number of times.
* `lineChain_mem`, `lineChain_not_mem`, `flip`: a line is a cycle that bounds nothing, so of a
  cycle `z` and `z + D` exactly one bounds (the four of the eight triangle cycles of page 35).
* `triangle_iff`: condition (A5) of page 50. For a triangle of three non-concurrent lines and a
  fourth line `Δ` through none of its vertices, a triangle cycle bounds iff `Δ` crosses an even
  number of its sides. The canonical orientation `ω` of the triangle is therefore read on the
  skeleton, and it does not depend on `Δ`.
* `line_cycle`, `seg_unique`: a cycle carried by one line is `0` or the line, so two segments of
  a line with the same ends are equal or complementary: segments are read on the skeleton.
* `SkelIso.triangle_map`: (A5) transported. A skeleton isomorphism carries a triangle cycle that
  bounds to one that bounds, whenever a fourth line avoids the vertices of the triangle.
* `path_bounds`: Jordan for the triangles of page 50. The triangle cut out by a face path
  `e1, e, e2` (the edge `e` and segments of the lines of `e1`, `e2` starting with them) bounds a
  union of faces. The proof is a parity count along the line of `e` (`edge_parity`).
* `corner2`, `path_map`, `full_simple`: **page 54 for simple arrangements.** At a vertex of two
  lines the corners are read on the skeleton; with `path_bounds`, `triangle_map` (a fourth line
  avoiding the triangle always exists when every vertex is on two lines) and `lift_iff`, every
  isomorphism of decomposed skeleta of two simple bigon-free arrangements lifts, uniquely: the
  skeleton functor is fully faithful on simple arrangements.
* `side_bounds`, `side_not`: (A4), at vertices of any multiplicity. Two edges leaving the ends of
  an edge `e` strictly on the same side (within the half turns after `d` and after `a0 d`) cut
  out with `e` a triangle that bounds; on opposite sides, one that does not. With
  `triangle_map`, whether they leave `e` on the same side is read on the skeleton when a fourth
  line avoids the triangle. `phi_period`: the `2ν` edge-ends at a vertex form one cycle of `φ`.
* `between_iff`, `side_tri`, `SkelIso.side_map`, `SkelIso.corner_map`: (A1)–(A3) at vertices of
  any multiplicity. Two edges at a vertex are adjacent iff no edge lies between them (on the side
  of each with respect to the other); sides are read by bounding triangles (`side_tri`), so a
  skeleton isomorphism carries corners to corners when every triangle has a fourth line.
* `path_map_gen`, `full_of_fourth`, `full_of_fourth'`: **page 54 away from `III₆`.** If every
  triangle of a bigon-free arrangement has a fourth line through none of its vertices
  (`FourthLine`, transported by `SkelIso.fourth_map`), every isomorphism of decomposed skeleta
  lifts uniquely: the skeleton functor is fully faithful there, multiple points included.
* `fourth_at`, `fourth_of_simpleCorner`, `full_of_simpleCorner`: a triangle with a vertex on
  only two lines always has a fourth line, so fullness holds whenever every triangle has a
  double vertex (`SimpleCorner`): a triangle without a fourth line has three multiple vertices.

**Not formalised.** The arrangements where some triangle has no fourth line avoiding its
vertices: (A6) and the complete quadrangle `III₆`. These are what remains of the page 54
theorem.
-/

namespace Grothendieck.Folder80Maps3

open Relation

/-- A relation contained in an equivalence closure has its equivalence closure inside. -/
theorem eqvGen_of_le {α : Type*} {r s : α → α → Prop} (h : ∀ x y, r x y → EqvGen s x y)
    {a b : α} (hab : EqvGen r a b) : EqvGen s a b := EqvGen.eqvGen_le h _ _ hab

/-- A set invariant under the generators of an equivalence closure is invariant under it. -/
theorem eqvGen_iff {α : Type*} {r : α → α → Prop} (S : α → Prop) (h : ∀ x y, r x y → (S x ↔ S y))
    {a b : α} (hab : EqvGen r a b) : S a ↔ S b :=
  (Equivalence.eqvGen_iff (r := fun x y => S x ↔ S y) ⟨fun _ => .rfl, .symm, .trans⟩).1
    (EqvGen.mono h _ _ hab)

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
/-- The face of a flag. -/
def face (d : D) : M.Face := Quot.mk _ d

instance [Finite D] : Finite M.Vtx := Quot.finite _
instance [Finite D] : Finite M.Edge := Quot.finite _
instance [Finite D] : Finite M.Face := Quot.finite _
noncomputable instance [Finite D] : Fintype M.Vtx := Fintype.ofFinite _
noncomputable instance [Finite D] : Fintype M.Edge := Fintype.ofFinite _
noncomputable instance [Finite D] : Fintype M.Face := Fintype.ofFinite _

/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face

variable {M}

@[simp] theorem vtx_a1 (d : D) : M.vtx (M.a1 d) = M.vtx d := (Quot.sound (.inl rfl)).symm
@[simp] theorem vtx_a2 (d : D) : M.vtx (M.a2 d) = M.vtx d := (Quot.sound (.inr rfl)).symm
@[simp] theorem edge_a0 (d : D) : M.edge (M.a0 d) = M.edge d := (Quot.sound (.inl rfl)).symm
@[simp] theorem edge_a2 (d : D) : M.edge (M.a2 d) = M.edge d := (Quot.sound (.inr rfl)).symm
@[simp] theorem face_a0 (d : D) : M.face (M.a0 d) = M.face d := (Quot.sound (.inl rfl)).symm
@[simp] theorem face_a1 (d : D) : M.face (M.a1 d) = M.face d := (Quot.sound (.inr rfl)).symm

theorem a0_eq_iff {x y : D} : M.a0 x = y ↔ x = M.a0 y :=
  ⟨fun h => h ▸ (M.a0_a0 x).symm, fun h => h ▸ M.a0_a0 y⟩
theorem a1_eq_iff {x y : D} : M.a1 x = y ↔ x = M.a1 y :=
  ⟨fun h => h ▸ (M.a1_a1 x).symm, fun h => h ▸ M.a1_a1 y⟩
theorem a2_eq_iff {x y : D} : M.a2 x = y ↔ x = M.a2 y :=
  ⟨fun h => h ▸ (M.a2_a2 x).symm, fun h => h ▸ M.a2_a2 y⟩

/-- An edge has exactly the four flags `d, a0 d, a2 d, a0 a2 d`. -/
theorem edge_eq {d e : D} :
    M.edge e = M.edge d ↔ e = d ∨ e = M.a0 d ∨ e = M.a2 d ∨ e = M.a0 (M.a2 d) := by
  constructor
  · intro h
    refine (eqvGen_iff (fun x => x = d ∨ x = M.a0 d ∨ x = M.a2 d ∨ x = M.a0 (M.a2 d)) ?_
      (Quot.eqvGen_exact h)).2 (.inl rfl)
    rintro x y (rfl | rfl)
    · simp only [a0_eq_iff, M.a0_a0]; tauto
    · simp only [a2_eq_iff, ← M.a0_a2, M.a2_a2]; tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem edge_four (d : D) : [d, M.a0 d, M.a2 d, M.a0 (M.a2 d)].Nodup := by
  have := M.a0_ne d; have := M.a2_ne d; have := M.a02_ne d; have := M.a0_ne (M.a2 d)
  simp_all [eq_comm, a0_eq_iff, M.a0_a0]

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

/-- A line whose flags all sit at two vertices `u, w` is not bigon-free. -/
theorem confined (hbf : BigonFree X.On) {l : L} {u w : X.M.Vtx}
    (H : ∀ e, X.line e = l → X.M.vtx e = u ∨ X.M.vtx e = w) : False := by
  obtain ⟨p, q, r, ⟨d1, rfl, h1⟩, ⟨d2, rfl, h2⟩, ⟨d3, rfl, h3⟩, h12, h13, h23⟩ := hbf l
  rcases H _ h1 with h1 | h1 <;> rcases H _ h2 with h2 | h2 <;> rcases H _ h3 with h3 | h3 <;>
    simp_all

/-- The connected line `l` stays in a set of vertices stable under `a0` along `l`. -/
theorem confine {l : L} (Z : X.M.Vtx → Prop)
    (h : ∀ x, X.line x = l → Z (X.M.vtx x) → Z (X.M.vtx (X.M.a0 x))) {d : D} (hd : X.line d = l)
    (hZ : Z (X.M.vtx d)) {e : D} (he : X.line e = l) : Z (X.M.vtx e) := by
  refine (eqvGen_iff (fun x => X.line x = l → Z (X.M.vtx x)) ?_ (X.conn d e (hd.trans he.symm))).1
    (fun _ => hZ) he
  rintro x y (rfl | ⟨h1, h2⟩)
  · rw [X.line_a0]
    exact ⟨fun h' hx => h _ hx (h' hx), fun h' hx => by
      simpa [X.M.a0_a0] using h _ (by rwa [X.line_a0]) (h' hx)⟩
  · rw [h1, h2]

/-- The flags form one orbit of `⟨a0, a1, a2⟩`. -/
theorem connected (d e : D) :
    EqvGen (fun x y => y = X.M.a0 x ∨ y = X.M.a1 x ∨ y = X.M.a2 x) d e := by
  have hv : ∀ {x y : D}, X.M.vtx x = X.M.vtx y →
      EqvGen (fun x y => y = X.M.a0 x ∨ y = X.M.a1 x ∨ y = X.M.a2 x) x y := fun h =>
    eqvGen_of_le (fun _ _ h => .rel _ _ (.inr h)) (Quot.eqvGen_exact h)
  have hl : ∀ {x y : D}, X.line x = X.line y →
      EqvGen (fun x y => y = X.M.a0 x ∨ y = X.M.a1 x ∨ y = X.M.a2 x) x y := fun h =>
    eqvGen_of_le (fun x y h => h.elim (fun h => .rel _ _ (.inl h)) fun h => hv h.1.symm)
      (X.conn _ _ h)
  by_cases h : X.line d = X.line e
  · exact hl h
  obtain ⟨v, ⟨⟨d1, h1, l1⟩, ⟨e1, h2, l2⟩⟩, -⟩ := X.meet _ _ h
  exact ((hl l1.symm).trans _ _ _ (hv (h1.trans h2.symm))).trans _ _ _ (hl l2)

/-- A function invariant under `a0, a1, a2` is constant. -/
theorem const_of_inv {α : Type*} (f : D → α) (h0 : ∀ d, f (X.M.a0 d) = f d)
    (h1 : ∀ d, f (X.M.a1 d) = f d) (h2 : ∀ d, f (X.M.a2 d) = f d) (d e : D) : f d = f e := by
  refine (eqvGen_iff (fun x => f x = f d) ?_ (connected (X := X) d e)).1 rfl |>.symm
  rintro x y (rfl | rfl | rfl) <;> simp [h0, h1, h2]

variable [Fintype D]

open Classical in
/-- The four flags of a line at a vertex. -/
theorem at_four {d x1 x2 x3 x4 : D} (hn : [x1, x2, x3, x4].Nodup)
    (hx : ∀ x ∈ [x1, x2, x3, x4], X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d) {f : D}
    (hf : X.M.vtx f = X.M.vtx d) (hl : X.line f = X.line d) : f ∈ [x1, x2, x3, x4] := by
  have h4 := X.pass d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have := Finset.eq_of_subset_of_card_le (s := [x1, x2, x3, x4].toFinset)
    (t := Finset.univ.filter fun e => X.M.vtx e = X.M.vtx d ∧ X.line e = X.line d)
    (fun x hx' => by simpa using hx _ (List.mem_toFinset.1 hx'))
    (by rw [h4, List.toFinset_card_of_nodup hn]; rfl)
  simpa [hf, hl] using (Finset.ext_iff.1 this f).2

/-- No loop: the two ends of an edge are distinct vertices. -/
theorem noLoop (hbf : BigonFree X.On) (d : D) : X.M.vtx (X.M.a0 d) ≠ X.M.vtx d := by
  intro h
  have hall : ∀ x ∈ [d, X.M.a0 d, X.M.a2 d, X.M.a0 (X.M.a2 d)],
      X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d := by
    simp [h, X.line_a0, X.line_a2, X.M.a0_a2]
  refine confined hbf (l := X.line d) (u := X.M.vtx d) (w := X.M.vtx d) fun e he => .inl ?_
  refine confine (fun t => t = X.M.vtx d) (fun x hx hxv => ?_) rfl rfl he
  have := at_four (edge_four d) hall hxv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> simp [h, X.M.a0_a0, X.M.a0_a2]

/-! ### Faithfulness -/

/-- At a vertex, the two flags of an edge-end are followed by flags of two different edges. -/
theorem edge_a1_a2_ne (hbf : BigonFree X.On) (u : D) :
    X.M.edge (X.M.a1 (X.M.a2 u)) ≠ X.M.edge (X.M.a1 u) := by
  intro e1
  have hn := noLoop hbf
  rcases edge_eq.1 e1 with k | k | k | k
  · exact X.M.a2_ne u (by simpa [X.M.a1_a1] using congrArg X.M.a1 k)
  · exact hn (X.M.a1 u) (by rw [← k]; simp)
  · -- `a1 a2 u = a2 a1 u`: the vertex of `u` has four flags only
    obtain ⟨e, hev, hel⟩ := X.two u
    have hS : ∀ x, X.M.vtx x = X.M.vtx u →
        x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨ x = X.M.a1 (X.M.a2 u) := fun x hx => by
      refine (eqvGen_iff (fun x => x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨
        x = X.M.a1 (X.M.a2 u)) ?_ (Quot.eqvGen_exact hx)).2 (.inl rfl)
      have k' : X.M.a2 (X.M.a1 (X.M.a2 u)) = X.M.a1 u := by rw [k, X.M.a2_a2]
      rintro x y (rfl | rfl)
      · simp only [a1_eq_iff, X.M.a1_a1]; tauto
      · simp only [a2_eq_iff, ← k, k', X.M.a2_a2]; tauto
    have hl1 : X.line (X.M.a1 u) ≠ X.line u := fun hl => hel <| by
      rcases hS e hev with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    classical
    have h4 := X.pass u
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
    have hsub : (Finset.univ.filter fun e => X.M.vtx e = X.M.vtx u ∧ X.line e = X.line u) ⊆
        {u, X.M.a2 u} := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hS x hx.1 with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  · exact hn (X.M.a2 (X.M.a1 u)) (by rw [← k]; simp)

omit [Fintype D] in
/-- **Faithfulness.** Two maps of flags `X → X'` commuting with `a1` (for instance two
isomorphisms of arrangements) that induce the same maps on vertices and on edges are equal. -/
theorem faithful {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}
    (hbf : BigonFree X'.On) {g g' : D → D'}
    (h1 : ∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) (h1' : ∀ d, g' (X.M.a1 d) = X'.M.a1 (g' d))
    (hv : ∀ d, X'.M.vtx (g d) = X'.M.vtx (g' d)) (he : ∀ d, X'.M.edge (g d) = X'.M.edge (g' d)) :
    g = g' := by
  funext d
  have hn := noLoop hbf
  rcases edge_eq.1 (he d) with h | h | h | h
  · exact h
  · exact (hn _ (by rw [← h, hv d])).elim
  · exact (edge_a1_a2_ne hbf _ (by have := he (X.M.a1 d); rwa [h1, h1', h] at this)).elim
  · exact (hn (X'.M.a2 (g' d)) (by rw [vtx_a2, ← hv d, h])).elim

/-! ### Chains mod 2 -/

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

omit [Fintype D] in
@[simp] theorem lineE_edge (d : D) : X.lineE (X.M.edge d) = X.line d := rfl

open Classical in
variable (X) in
/-- The incidence matrix vertices × edges: the boundary `∂₁`. -/
noncomputable def incM : Matrix X.M.Vtx X.M.Edge (ZMod 2) :=
  Matrix.of fun v e => if X.Inc v e then 1 else 0

open Classical in
variable (X) in
/-- The boundary `∂₂` of faces: an edge is counted once for each of its two sides. -/
noncomputable def bdM : Matrix X.M.Edge X.M.Face (ZMod 2) :=
  Matrix.of fun e f =>
    (if X.M.face e.out = f then 1 else 0) + (if X.M.face (X.M.a2 e.out) = f then 1 else 0)

variable (X) in
/-- The cycles `Z₁ = ker ∂₁`. -/
noncomputable abbrev Z1 := LinearMap.ker X.incM.mulVecLin

variable (X) in
/-- The boundaries `B₁ = im ∂₂`. -/
noncomputable abbrev B1 := LinearMap.range X.bdM.mulVecLin

open Classical in
variable (X) in
/-- The chain of a line: its edges. -/
noncomputable def lineChain (l : L) : X.M.Edge → ZMod 2 := fun e => if X.lineE e = l then 1 else 0

omit [Fintype D] in
theorem edge_surj (e : X.M.Edge) : ∃ d, X.M.edge d = e := Quot.exists_rep e

open Classical in
theorem incM_mulVec (c : X.M.Edge → ZMod 2) (v : X.M.Vtx) :
    (X.incM *ᵥ c) v = ∑ e, if X.Inc v e then c e else 0 := by
  simp [incM, Matrix.mulVec, dotProduct]

theorem bd_apply (S : X.M.Face → ZMod 2) (d : D) :
    (X.bdM *ᵥ S) (X.M.edge d) = S (X.M.face d) + S (X.M.face (X.M.a2 d)) := by
  classical
  have : ∀ e, (X.bdM *ᵥ S) e = S (X.M.face e.out) + S (X.M.face (X.M.a2 e.out)) := fun e => by
    simp [bdM, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  rw [this]
  rcases edge_eq.1 (Quot.out_eq (X.M.edge d)) with h | h | h | h <;>
    simp [h, ← X.M.a0_a2, X.M.a2_a2, add_comm]

/-- The flags at a vertex on a given edge are `d` and `a2 d`. -/
theorem at_edge (hbf : BigonFree X.On) {d x : D} :
    X.M.vtx x = X.M.vtx d ∧ X.M.edge x = X.M.edge d ↔ x = d ∨ x = X.M.a2 d := by
  refine ⟨fun ⟨hv, he⟩ => ?_, by rintro (rfl | rfl) <;> simp⟩
  rcases edge_eq.1 he with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact (noLoop hbf _ hv).elim
  · exact .inr rfl
  · exact (noLoop hbf (X.M.a2 d) (by rw [hv, vtx_a2])).elim

omit [Fintype D] in
theorem inc_iff (d : D) (v : X.M.Vtx) :
    X.Inc v (X.M.edge d) ↔ v = X.M.vtx d ∨ v = X.M.vtx (X.M.a0 d) := by
  constructor
  · rintro ⟨x, rfl, hx⟩
    rcases edge_eq.1 hx with rfl | rfl | rfl | rfl <;> simp [X.M.a0_a2]
  · rintro (rfl | rfl)
    exacts [⟨d, rfl, rfl⟩, ⟨_, rfl, edge_a0 d⟩]

open Classical in
theorem sum_inc (hbf : BigonFree X.On) (d : D) (g : X.M.Vtx → ZMod 2) :
    ∑ v, (if X.Inc v (X.M.edge d) then g v else 0) = g (X.M.vtx d) + g (X.M.vtx (X.M.a0 d)) := by
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun v => X.Inc v (X.M.edge d)) = {X.M.vtx d, X.M.vtx (X.M.a0 d)} := by
    ext v; simp [inc_iff]
  rw [this, Finset.sum_pair (noLoop hbf d).symm]

theorem two_eq (a b : ZMod 2) (h : a + b = 0) : a = b := by
  revert a b; decide

theorem add_self' (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

omit [Fintype D] in
/-- A function on vertices that is constant across every edge is constant. -/
theorem vtx_const {g : X.M.Vtx → ZMod 2} (h : ∀ d, g (X.M.vtx d) = g (X.M.vtx (X.M.a0 d)))
    (v w : X.M.Vtx) : g v = g w := by
  induction v using Quot.ind; induction w using Quot.ind
  exact const_of_inv (X := X) (fun d => g (X.M.vtx d)) (fun d => (h d).symm) (by simp) (by simp)
    _ _

omit [Fintype D] in
theorem finrank_ker_le {V W : Type*} [Fintype V] [AddCommGroup W] [Module (ZMod 2) W]
    {f : (V → ZMod 2) →ₗ[ZMod 2] W}
    (h : ∀ g ∈ LinearMap.ker f, ∀ v w, g v = g w) : Module.finrank (ZMod 2) (LinearMap.ker f) ≤ 1 := by
  refine (Submodule.finrank_mono (t := Submodule.span (ZMod 2) {fun _ => 1}) fun g hg => ?_).trans
    ((finrank_span_le_card _).trans (by simp))
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v0⟩⟩
  · exact Subsingleton.elim (0 : V → ZMod 2) g ▸ Submodule.zero_mem _
  · exact Submodule.mem_span_singleton.2 ⟨g v0, funext fun v => by simp [h g hg v0 v]⟩

/-- `∂₁ ∂₂ = 0`: boundaries are cycles. -/
theorem B1_le_Z1 (hbf : BigonFree X.On) : X.B1 ≤ X.Z1 := by
  classical
  rintro _ ⟨S, rfl⟩
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext v
  have hsum : ∑ x ∈ Finset.univ.filter (fun x => X.M.vtx x = v), S (X.M.face x) = 0 :=
    Finset.sum_involution (fun x _ => X.M.a1 x) (fun _ _ => by simp [add_self'])
      (fun x _ _ => X.M.a1_ne x) (fun _ hx => by simpa using hx) (fun x _ => X.M.a1_a1 x)
  rw [← Finset.sum_fiberwise_of_maps_to (g := X.M.edge) (t := Finset.univ) (by simp)] at hsum
  rw [incM_mulVec, Pi.zero_apply]
  refine (Finset.sum_congr rfl fun e _ => ?_).trans hsum
  obtain ⟨d, rfl⟩ := edge_surj e
  split_ifs with h
  · obtain ⟨d', rfl, he⟩ := h
    have : Finset.filter (fun x => X.M.edge x = X.M.edge d)
        (Finset.univ.filter fun x => X.M.vtx x = X.M.vtx d') = {d', X.M.a2 d'} := by
      ext; simp [← at_edge hbf, he]
    rw [this, Finset.sum_pair (X.M.a2_ne d').symm, ← bd_apply, he]
  · exact (Finset.sum_eq_zero fun x hx => (h ⟨x, by simpa using hx⟩).elim).symm

/-- **`Z₁/B₁` has dimension at most `1`** (from `χ = 1`): this is the page 42 relation
`c₂ = c(K)`, the first Betti number of the skeleton. -/
theorem finrank_Z1_le (hbf : BigonFree X.On) :
    Module.finrank (ZMod 2) X.Z1 ≤ Module.finrank (ZMod 2) X.B1 + 1 := by
  classical
  show Module.finrank _ (LinearMap.ker _) ≤ Module.finrank _ (LinearMap.range _) + 1
  have k1 : Module.finrank (ZMod 2) (LinearMap.ker X.incMᵀ.mulVecLin) ≤ 1 := by
    refine finrank_ker_le fun g hg => vtx_const fun d => two_eq _ _ ?_
    have := congrFun (LinearMap.mem_ker.1 hg) (X.M.edge d)
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, incM,
      Matrix.of_apply, ite_mul, one_mul, zero_mul, Pi.zero_apply] at this
    rwa [sum_inc hbf] at this
  have k2 : Module.finrank (ZMod 2) (LinearMap.ker X.bdM.mulVecLin) ≤ 1 := by
    refine finrank_ker_le fun S hS f f' => ?_
    have h : ∀ d, S (X.M.face d) = S (X.M.face (X.M.a2 d)) := fun d => two_eq _ _ <| by
      have := congrFun (LinearMap.mem_ker.1 hS) (X.M.edge d)
      rwa [Matrix.mulVecLin_apply, bd_apply] at this
    induction f using Quot.ind; induction f' using Quot.ind
    exact const_of_inv (X := X) (fun d => S (X.M.face d)) (by simp) (by simp) (h · |>.symm) _ _
  have r1 := LinearMap.finrank_range_add_finrank_ker X.incM.mulVecLin
  have r2 := LinearMap.finrank_range_add_finrank_ker X.incMᵀ.mulVecLin
  have r3 := LinearMap.finrank_range_add_finrank_ker X.bdM.mulVecLin
  have rt := Matrix.rank_transpose X.incM
  simp only [Module.finrank_fintype_fun_eq_card] at r1 r2 r3
  have he := X.euler
  simp only [GMap.euler, Nat.card_eq_fintype_card] at he
  unfold Matrix.rank at rt
  omega

end Chains

/-! ### The rotation at a vertex -/

variable (X) in
/-- The rotation `φ = a2 a1` around a vertex: from an edge-end to the next one. -/
def phi : Equiv.Perm D :=
  Function.Involutive.toPerm X.M.a2 X.M.a2_a2 * Function.Involutive.toPerm X.M.a1 X.M.a1_a1

omit [Fintype D] in
theorem phi_apply (x : D) : X.phi x = X.M.a2 (X.M.a1 x) := rfl

omit [Fintype D] in
theorem phi_inv_apply (x : D) : X.phi⁻¹ x = X.M.a1 (X.M.a2 x) :=
  (Equiv.Perm.inv_eq_iff_eq).2 (by simp [phi_apply, X.M.a1_a1, X.M.a2_a2])

omit [Fintype D] in
theorem a2_phi (x : D) : X.M.a2 (X.phi x) = X.M.a1 x := X.M.a2_a2 _

omit [Fintype D] in
/-- A function invariant under `φ` is invariant under its powers. -/
theorem zpow_inv {α : Type*} (g : D → α) (h : ∀ x, g (X.phi x) = g x) (k : ℤ) (x : D) :
    g ((X.phi ^ k) x) = g x := by
  induction k with
  | zero => simp
  | succ n ih => rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, h, ih]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, ← ih,
      ← h (X.phi⁻¹ _)]
    exact congrArg g ((Equiv.eq_symm_apply X.phi).mp rfl)

omit [Fintype D] in
@[simp] theorem vtx_phi1 (x : D) : X.M.vtx (X.phi x) = X.M.vtx x := by simp [phi_apply]

omit [Fintype D] in
@[simp] theorem vtx_phi (k : ℤ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x :=
  zpow_inv _ (fun x => by simp [phi_apply]) k x

omit [Fintype D] in
@[simp] theorem vtx_phi' (k : ℕ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x := by
  simpa using vtx_phi (X := X) k x

omit [Fintype D] in
/-- `a2 φ^k = φ^{-k} a2`. -/
theorem a2_zpow (k : ℤ) (x : D) : X.M.a2 ((X.phi ^ k) x) = (X.phi ^ (-k)) (X.M.a2 x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, a2_phi,
      show -(1 + (n : ℤ)) = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, ← ih, zpow_neg_one,
      phi_inv_apply, X.M.a2_a2]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one,
      phi_inv_apply, ← phi_apply, ih, ← Equiv.Perm.mul_apply, ← zpow_one_add]
    congr 2; ring

omit [Fintype D] in
/-- The two orbits of `φ` at a vertex are exchanged by `a2`: `a2 φ^i x ≠ φ^j x`. -/
theorem a2_ne_zpow (i j : ℤ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  intro h
  rw [a2_zpow] at h
  have h' : X.M.a2 x = (X.phi ^ (i + j)) x := by
    have := congrArg (X.phi ^ i) h
    rwa [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply,
      ← Equiv.Perm.mul_apply, ← zpow_add] at this
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' (i + j)
  · apply X.M.a2_ne ((X.phi ^ t) x)
    rw [a2_zpow, h', ht, ← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2; ring
  · apply X.M.a1_ne ((X.phi ^ t) x)
    rw [← a2_phi, ← Equiv.Perm.mul_apply, ← zpow_one_add, a2_zpow, h', ht, ← Equiv.Perm.mul_apply,
      ← zpow_add]
    congr 2; ring

omit [Fintype D] in
/-- The flags at the vertex of `x` are the `φ^k x` and the `a2 φ^k x`. -/
theorem vtx_orbit {x y : D} (h : X.M.vtx y = X.M.vtx x) :
    ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x) := by
  let S : D → Prop := fun y => ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x)
  have c1 : ∀ u, S u → S (X.M.a1 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨1 + k, .inr (by rw [zpow_one_add, Equiv.Perm.mul_apply, a2_phi])⟩
    · exact ⟨-1 + k, .inl (by rw [zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, phi_inv_apply])⟩
  have c2 : ∀ u, S u → S (X.M.a2 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨k, .inr rfl⟩
    · exact ⟨k, .inl (X.M.a2_a2 _)⟩
  refine (eqvGen_iff S ?_ (Quot.eqvGen_exact h)).2 ⟨0, .inl rfl⟩
  rintro u w (rfl | rfl)
  · exact ⟨c1 u, fun h => by simpa [X.M.a1_a1] using c1 _ h⟩
  · exact ⟨c2 u, fun h => by simpa [X.M.a2_a2] using c2 _ h⟩

open Classical in
variable (X) in
/-- The number `ν(v)` of lines through a vertex. -/
noncomputable def nu (v : X.M.Vtx) : ℕ :=
  ((Finset.univ.filter fun d => X.M.vtx d = v).image X.line).card

variable (X) in
/-- **Going straight** (page 60; (22) of page 41): half a turn around a vertex of `ν` lines,
`ν` edge-ends further, one finds the same line. -/
def Straight : Prop := ∀ d, X.line ((X.phi ^ X.nu (X.M.vtx d)) d) = X.line d

open Classical in
theorem card_vtx (x : D) :
    (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x).card = 4 * X.nu (X.M.vtx x) := by
  rw [Finset.card_eq_sum_card_image X.line, nu, Finset.sum_const_nat (m := 4), mul_comm]
  intro l hl
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hl
  have h4 := X.pass e
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  rw [Finset.filter_filter, ← h4]
  congr 1; ext a; simp [(Finset.mem_filter.1 he).2]

open Classical in
/-- A period of `φ` at a flag is at least the number `2ν` of edge-ends. -/
theorem four_nu_le (x : D) {q : ℕ} (hq : 0 < q) (h : (X.phi ^ q) x = x) :
    4 * X.nu (X.M.vtx x) ≤ 2 * q := by
  rw [← card_vtx]
  have hsub : (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x) ⊆
      ((Finset.range q) ×ˢ (Finset.univ : Finset Bool)).image
        fun p => if p.2 then X.M.a2 ((X.phi ^ p.1) x) else (X.phi ^ p.1) x := by
    intro y hy
    obtain ⟨k, hk⟩ := vtx_orbit (Finset.mem_filter.1 hy).2
    have hr : (X.phi ^ k) x = (X.phi ^ (k % q).toNat) x := by
      have h' : ((X.phi ^ (q : ℤ)) ^ (k / q)) x = x :=
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by simpa using h) _
      conv_lhs => rw [← Int.emod_add_mul_ediv k q, zpow_add, Equiv.Perm.mul_apply, zpow_mul, h']
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    have hlt : (k % q).toNat < q := by
      have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < q); omega
    rcases hk with rfl | rfl
    exacts [Finset.mem_image.2 ⟨((k % q).toNat, false), by simp [hlt], by simp [hr]⟩,
      Finset.mem_image.2 ⟨((k % q).toNat, true), by simp [hlt], by simp [hr]⟩]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [mul_comm]

omit [Fintype D] in
theorem a2_ne_pow (i j : ℕ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  simpa using a2_ne_zpow (X := X) i j x

/-- Distinct powers below `2ν` of `φ` move a flag to distinct flags. -/
theorem pow_ne (y : D) {a b : ℕ} (hab : a < b) (hb : b < 2 * X.nu (X.M.vtx y)) :
    (X.phi ^ a) y ≠ (X.phi ^ b) y := fun h => by
  have := four_nu_le ((X.phi ^ a) y) (q := b - a) (by omega) (by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hab.le, ← h])
  rw [vtx_phi'] at this
  omega

theorem straight_pow (hs : X.Straight) (y : D) (i : ℕ) :
    X.line ((X.phi ^ (i + X.nu (X.M.vtx y))) y) = X.line ((X.phi ^ i) y) := by
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]
  simpa using hs ((X.phi ^ i) y)

open Classical in
/-- The `ν` edge-ends met in half a turn around a vertex carry distinct lines. -/
theorem line_inj (hs : X.Straight) (y : D) {i j : ℕ} (hij : i < j)
    (hj : j < X.nu (X.M.vtx y)) : X.line ((X.phi ^ i) y) ≠ X.line ((X.phi ^ j) y) := by
  intro hl
  set ν := X.nu (X.M.vtx y)
  have hn : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].Nodup := by
    have p : ∀ {a b : ℕ}, a < b → b < 2 * ν → (X.phi ^ a) y ≠ (X.phi ^ b) y :=
      fun h h' => pow_ne y h h'
    have q := a2_ne_pow (X := X)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨p hij (by omega), p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i i y h.symm⟩, ⟨p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i j y h.symm⟩, ⟨p (by omega) (by omega), fun h => q i _ y h.symm⟩,
      fun h => q i _ y h.symm⟩
  have h4 := X.pass ((X.phi ^ i) y)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have hsub : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].toFinset ⊆ Finset.univ.filter fun e =>
        X.M.vtx e = X.M.vtx ((X.phi ^ i) y) ∧ X.line e = X.line ((X.phi ^ i) y) := by
    intro e he
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [ν, hl, X.line_a2, straight_pow hs y i, straight_pow hs y j]
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, h4] at this
  simp at this

open Classical in
/-- **Half a turn meets every other line once**: in `φ x, …, φ^ν x` each line through the
vertex appears exactly once. -/
theorem rot_card (hs : X.Straight) (y : D) {m : L} (hm : X.On (X.M.vtx y) m) :
    ((Finset.range (X.nu (X.M.vtx y))).filter fun i => X.line ((X.phi ^ i) y) = m).card = 1 := by
  set T := (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx y).image X.line
  have hinj : Set.InjOn (fun i => X.line ((X.phi ^ i) y)) ↑(Finset.range (X.nu (X.M.vtx y))) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hij | rfl | hij
    exacts [(line_inj hs y hij hj h).elim, rfl, (line_inj hs y hij hi h.symm).elim]
  have hsub : (Finset.range (X.nu (X.M.vtx y))).image (fun i => X.line ((X.phi ^ i) y)) ⊆ T :=
    fun l hl => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      exact Finset.mem_image.2 ⟨_, by simp, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_image_of_injOn hinj, Finset.card_range]; rfl)
  obtain ⟨d, hd, rfl⟩ := hm
  obtain ⟨i, hi, hil⟩ := Finset.mem_image.1 (heq ▸ Finset.mem_image.2 ⟨d, by simp [hd], rfl⟩ :
    X.line d ∈ (Finset.range (X.nu (X.M.vtx y))).image (fun i => X.line ((X.phi ^ i) y)))
  refine Finset.card_eq_one.2 ⟨i, Finset.ext fun k => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun ⟨hk, hkl⟩ => hinj hk hi (hkl.trans hil.symm), fun h => h ▸ ⟨hi, hil⟩⟩

open Classical in
/-- The two edges of the line of `x` at the vertex of `x`: those of `x` and of `φ^ν x`. -/
theorem line_edges (hbf : BigonFree X.On) (hs : X.Straight) (x : D) :
    (Finset.univ.filter fun e => X.Inc (X.M.vtx x) e ∧ X.lineE e = X.line x) =
      {X.M.edge x, X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x)} ∧
    X.M.edge x ≠ X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x) := by
  set ν := X.nu (X.M.vtx x)
  set x' := (X.phi ^ ν) x
  have hx' : X.line x' = X.line x := hs x
  have hν : 0 < ν := Finset.card_pos.2 ⟨X.line x, Finset.mem_image.2 ⟨x, by simp, rfl⟩⟩
  have hxx' : x ≠ x' := by simpa using pow_ne (X := X) x hν (by omega)
  have hn : [x, X.M.a2 x, x', X.M.a2 x'].Nodup := by
    have q := a2_ne_pow (X := X)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨(X.M.a2_ne x).symm, hxx', fun h => by simpa using q ν 0 x h.symm⟩,
      ⟨by simpa using q 0 ν x, fun h => hxx' (by simpa [X.M.a2_a2] using congrArg X.M.a2 h)⟩,
      (X.M.a2_ne x').symm⟩
  refine ⟨?_, fun h => ?_⟩
  · ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨d, hdv, rfl⟩, hdl⟩
      have := at_four hn (by simp [x', hx', X.line_a2]) hdv hdl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · rintro (rfl | rfl)
      exacts [⟨⟨x, rfl, rfl⟩, rfl⟩, ⟨⟨x', by simp [x'], rfl⟩, hx'⟩]
  rcases edge_eq.1 h.symm with h | h | h | h
  · exact hxx' h.symm
  · exact noLoop hbf x (by rw [← h]; simp [x'])
  · exact a2_ne_pow (X := X) 0 ν x (by simpa using h.symm)
  · exact noLoop hbf (X.M.a2 x) (by rw [← h]; simp [x'])

/-! ### The parity lemma -/

section Parity

open Matrix

/-- Turning by `φ` across an edge of the boundary `∂S` changes side of `S`. -/
theorem face_phi (S : X.M.Face → ZMod 2) (y : D) :
    S (X.M.face (X.phi y)) = S (X.M.face y) + (X.bdM *ᵥ S) (X.M.edge (X.phi y)) := by
  rw [show X.M.edge (X.phi y) = X.M.edge (X.M.a1 y) by simp [phi_apply], bd_apply, face_a1,
    ← add_assoc, add_self', zero_add]
  rfl

theorem face_phi_pow (S : X.M.Face → ZMod 2) (y : D) (n : ℕ) :
    S (X.M.face ((X.phi ^ n) y)) =
      S (X.M.face y) + ∑ i ∈ Finset.range n, (X.bdM *ᵥ S) (X.M.edge ((X.phi ^ (i + 1)) y)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, face_phi S, ih, Finset.sum_range_succ,
      add_assoc, ← Equiv.Perm.mul_apply, ← pow_succ']

open Classical in
/-- **The parity lemma.** Let `z = ∂S` be a boundary and `Δ` a line carrying no edge of `z`,
such that at each vertex of `Δ` the cycle `z` either is absent or goes straight across along a
single other line. Then `Δ` meets `z` in an even number of vertices: a closed curve crosses the
boundary of a union of faces an even number of times. -/
theorem parity (hbf : BigonFree X.On) (hs : X.Straight) (S : X.M.Face → ZMod 2) (Δ : L)
    (h1 : ∀ e, X.lineE e = Δ → (X.bdM *ᵥ S) e = 0)
    (h2 : ∀ w, X.On w Δ → (∀ e, X.Inc w e → (X.bdM *ᵥ S) e = 0) ∨
      ∃ m, m ≠ Δ ∧ X.On w m ∧ ∀ e, X.Inc w e → (X.bdM *ᵥ S) e = if X.lineE e = m then 1 else 0) :
    ∑ w, (if X.On w Δ ∧ ∃ e, X.Inc w e ∧ (X.bdM *ᵥ S) e ≠ 0 then (1 : ZMod 2) else 0) = 0 := by
  set z := X.bdM *ᵥ S
  let μ : X.M.Edge → ZMod 2 := fun e => S (X.M.face e.out)
  have hμ : ∀ d, X.line d = Δ → μ (X.M.edge d) = S (X.M.face d) := fun d hd => by
    have h0 : S (X.M.face (X.M.a2 d)) = S (X.M.face d) :=
      (two_eq _ _ (by rw [add_comm, ← bd_apply]; exact h1 _ hd))
    rcases edge_eq.1 (Quot.out_eq (X.M.edge d)) with h | h | h | h <;> simp [μ, h, h0]
  -- the local count at a vertex of `Δ`
  have loc : ∀ w, X.On w Δ → ∑ e, (if X.Inc w e ∧ X.lineE e = Δ then μ e else 0) =
      if ∃ e, X.Inc w e ∧ z e ≠ 0 then 1 else 0 := by
    rintro w ⟨x, rfl, hx⟩
    set ν := X.nu (X.M.vtx x)
    set x' := (X.phi ^ ν) x
    have hx' : X.line x' = Δ := (hs x).trans hx
    obtain ⟨hfil, hee⟩ := line_edges hbf hs x
    rw [hx] at hfil
    rw [← Finset.sum_filter, hfil, Finset.sum_pair hee, hμ x hx, hμ x' hx', face_phi_pow S]
    rcases h2 _ ⟨x, rfl, hx⟩ with h | ⟨m, hm, hmw, hz⟩
    · rw [Finset.sum_eq_zero fun i _ => h _ ⟨_, by simp, rfl⟩, ite_eq_right fun ⟨e, he, hz⟩ => hz (h e he),
        add_zero, add_self']
    · obtain ⟨d, hdv, rfl⟩ := hmw
      rw [ite_eq_left ⟨X.M.edge d, ⟨d, hdv, rfl⟩, by rw [hz _ ⟨d, hdv, rfl⟩]; simp⟩, ← add_assoc,
        add_self', zero_add]
      have hr := rot_card hs (X.phi x) (m := X.line d) ⟨d, by rw [vtx_phi1]; exact hdv, rfl⟩
      rw [vtx_phi1] at hr
      have : ∀ i ∈ Finset.range ν, z (X.M.edge ((X.phi ^ (i + 1)) x)) =
          if X.line ((X.phi ^ i) (X.phi x)) = X.line d then 1 else 0 := fun i _ => by
        rw [hz _ ⟨_, by simp, rfl⟩, lineE_edge, ← Equiv.Perm.mul_apply, ← pow_succ]
      rw [Finset.sum_congr rfl this, Finset.sum_boole, hr]
      simp
  -- the global count: every edge of `Δ` has two ends
  calc ∑ w, (if X.On w Δ ∧ ∃ e, X.Inc w e ∧ z e ≠ 0 then (1 : ZMod 2) else 0)
      = ∑ w, ∑ e, (if X.Inc w e ∧ X.lineE e = Δ then μ e else 0) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hw : X.On w Δ
        · rw [loc w hw]; simp [hw]
        · rw [ite_eq_right (fun h => hw h.1), Finset.sum_eq_zero fun e _ =>
            ite_eq_right fun ⟨⟨d, h1, h2⟩, hd⟩ => hw ⟨d, h1, by subst h2; exact hd⟩]
    _ = ∑ e, ∑ w, (if X.Inc w e then (if X.lineE e = Δ then μ e else 0) else 0) := by
        rw [Finset.sum_comm]; simp only [ite_and]
    _ = 0 := Finset.sum_eq_zero fun e _ => by
        obtain ⟨d, rfl⟩ := edge_surj e
        rw [sum_inc hbf d (fun _ => if X.lineE (X.M.edge d) = Δ then μ (X.M.edge d) else 0),
          add_self']

omit [Fintype D] in
theorem on_of_inc {w : X.M.Vtx} {e : X.M.Edge} (h : X.Inc w e) : X.On w (X.lineE e) := by
  obtain ⟨d, rfl, rfl⟩ := h; exact ⟨d, rfl, rfl⟩

omit [Fintype D] in
/-- A chain supported on the line `x` vanishes at the edges of a vertex off `x`. -/
theorem off_line {x : L} {P : X.M.Edge → ZMod 2} (hP : ∀ e, P e ≠ 0 → X.lineE e = x)
    {w : X.M.Vtx} (hw : ¬X.On w x) {e : X.M.Edge} (he : X.Inc w e) : P e = 0 :=
  by_contra fun h => hw (hP e h ▸ on_of_inc he)

open Classical in
/-- A line is a cycle. -/
theorem lineChain_mem (hbf : BigonFree X.On) (hs : X.Straight) (l : L) : X.lineChain l ∈ X.Z1 := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  funext v
  rw [incM_mulVec, Pi.zero_apply]
  simp only [lineChain, ← ite_and, Finset.sum_boole]
  by_cases hv : X.On v l
  · obtain ⟨x, rfl, rfl⟩ := hv
    rw [(line_edges hbf hs x).1, Finset.card_pair (line_edges hbf hs x).2]; rfl
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun e _ ⟨h1, h2⟩ => hv (h2 ▸ on_of_inc h1))]
    rfl

open Classical in
/-- **A line does not bound.** Another line `Δ` meets it once, straight across. -/
theorem lineChain_not_mem (hbf : BigonFree X.On) (hs : X.Straight) {a Δ : L} (h : a ≠ Δ) :
    X.lineChain a ∉ X.B1 := by
  rintro ⟨S, hS⟩
  simp only [Matrix.mulVecLin_apply] at hS
  have key := parity hbf hs S Δ (fun e he => by simp [hS, lineChain, he, h.symm]) fun w _ => by
    by_cases hw : X.On w a
    · exact .inr ⟨a, h, hw, fun e _ => by rw [hS]; rfl⟩
    · exact .inl fun e he => by rw [hS]; exact off_line (fun e h' => by
        simp only [lineChain] at h'; by_contra hc; exact h' (by simp [hc])) hw he
  obtain ⟨v, ⟨hva, hvΔ⟩, hu⟩ := X.meet a Δ h
  rw [Finset.sum_eq_single v] at key
  · rw [ite_eq_left] at key
    · exact one_ne_zero key
    obtain ⟨d, hd, rfl⟩ := hva
    exact ⟨hvΔ, X.M.edge d, ⟨d, hd, rfl⟩, by simp [hS, lineChain]⟩
  · rintro w - hw
    refine ite_eq_right fun ⟨h1, e, he, h2⟩ => hw (hu w ⟨?_, h1⟩)
    rw [hS] at h2
    simp only [lineChain, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h2
    exact h2 ▸ on_of_inc he
  · simp

/-- Since `Z₁/B₁` has dimension `≤ 1` and a line does not bound, every cycle bounds, or bounds
after adding any line. -/
theorem Z1_cases (hbf : BigonFree X.On) (hs : X.Straight) {a Δ : L} (h : a ≠ Δ)
    {z : X.M.Edge → ZMod 2} (hz : z ∈ X.Z1) : z ∈ X.B1 ∨ z + X.lineChain a ∈ X.B1 := by
  set c := X.lineChain a
  have hc := lineChain_not_mem hbf hs h
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [show X.lineChain a = 0 from h0]; exact Submodule.zero_mem _)
  have hinf : X.B1 ⊓ Submodule.span (ZMod 2) {c} = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun y ⟨hy, hy'⟩ => ?_
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    by_cases ht : t = 0
    · simp [ht]
    · exact (hc (by simpa [smul_smul, inv_mul_cancel₀ ht] using Submodule.smul_mem _ t⁻¹ hy)).elim
  have hle : X.B1 ⊔ Submodule.span (ZMod 2) {c} ≤ X.Z1 :=
    sup_le (B1_le_Z1 hbf) ((Submodule.span_singleton_le_iff_mem _ _).2 (lineChain_mem hbf hs a))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X.B1 (Submodule.span (ZMod 2) {c})
  rw [hinf, finrank_bot, finrank_span_singleton hc0] at hdim
  have heq := Submodule.eq_of_le_of_finrank_le hle (by have := finrank_Z1_le hbf; omega)
  obtain ⟨b, hb, y, hy, rfl⟩ := Submodule.mem_sup.1 (heq ▸ hz)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rcases zmod2_cases t with rfl | rfl
  · left; rwa [zero_smul, add_zero]
  · right
    rwa [one_smul, add_assoc, show c + c = 0 from funext fun e => add_self' _, add_zero]

omit [Fintype D] in
theorem meet_eq {l l' : L} (h : l ≠ l') {v w : X.M.Vtx} (hv : X.On v l) (hv' : X.On v l')
    (hw : X.On w l) (hw' : X.On w l') : v = w := by
  obtain ⟨u, -, hu⟩ := X.meet l l' h
  exact (hu v ⟨hv, hv'⟩).trans (hu w ⟨hw, hw'⟩).symm

open Classical in
/-- A segment `P` of the line `x` (a chain on `x` with boundary `p + q`) takes the same value on
the two edges of `x` at any vertex other than `p, q`. -/
theorem seg_val (hbf : BigonFree X.On) (hs : X.Straight) {x : L} {p q : X.M.Vtx}
    {P : X.M.Edge → ZMod 2} (hP : ∀ e, P e ≠ 0 → X.lineE e = x)
    (hb : X.incM *ᵥ P = Pi.single p 1 + Pi.single q 1) {w : X.M.Vtx} (hp : w ≠ p) (hq : w ≠ q)
    {ex : X.M.Edge} (hex : X.lineE ex = x) (hw : X.Inc w ex) (e : X.M.Edge) (he : X.Inc w e) :
    P e = if X.lineE e = x then P ex else 0 := by
  have h0 := congrFun hb w
  rw [incM_mulVec] at h0
  simp only [Pi.add_apply, Pi.single_apply, hp, hq, ite_false, add_zero] at h0
  obtain ⟨y, rfl, hy⟩ := hw
  have hyx : X.line y = x := by rw [← hex, ← hy]; rfl
  obtain ⟨hfil, hee⟩ := line_edges hbf hs y
  rw [hyx] at hfil
  rw [Finset.sum_congr rfl (g := fun e => if X.Inc (X.M.vtx y) e ∧ X.lineE e = x then P e else 0)
    (fun e _ => by
      by_cases h1 : X.Inc (X.M.vtx y) e <;> by_cases h2 : X.lineE e = x <;> simp [h1, h2]
      exact by_contra fun h => h2 (hP e h)), ← Finset.sum_filter, hfil,
    Finset.sum_pair hee] at h0
  have h0 := two_eq _ _ h0
  have mem : ∀ e, X.Inc (X.M.vtx y) e → X.lineE e = x →
      e = X.M.edge y ∨ e = X.M.edge ((X.phi ^ X.nu (X.M.vtx y)) y) := fun e h1 h2 => by
    have : e ∈ Finset.univ.filter fun e => X.Inc (X.M.vtx y) e ∧ X.lineE e = x := by simp [h1, h2]
    rw [hfil] at this; simpa using this
  split_ifs with h
  · rcases mem e he h with rfl | rfl <;> rcases mem ex ⟨y, rfl, hy⟩ hex with h' | h' <;>
      rw [h'] <;> simp [h0]
  · exact by_contra fun h' => h (hP e h')

open Classical in
theorem ind_val {Δ x : L} {z : X.M.Edge → ZMod 2} {w : X.M.Vtx} (hw : X.On w Δ) {t : ZMod 2}
    (hz : ∀ e, X.Inc w e → z e = if X.lineE e = x then t else 0) {ex : X.M.Edge}
    (hex : X.Inc w ex) (hx : X.lineE ex = x) :
    (if X.On w Δ ∧ ∃ e, X.Inc w e ∧ z e ≠ 0 then (1 : ZMod 2) else 0) = t := by
  rcases zmod2_cases t with rfl | rfl
  · exact ite_eq_right fun ⟨_, e, he, h⟩ => h (by rw [hz e he]; simp)
  · exact ite_eq_left ⟨hw, ex, hex, by rw [hz ex hex, ite_eq_left hx]; simp⟩

omit [Fintype D] in
open Classical in
theorem cross_of {Δ x : L} {z : X.M.Edge → ZMod 2} {w : X.M.Vtx} (hxΔ : x ≠ Δ) (hwx : X.On w x)
    {t : ZMod 2} (hz : ∀ e, X.Inc w e → z e = if X.lineE e = x then t else 0) :
    (∀ e, X.Inc w e → z e = 0) ∨
      ∃ m, m ≠ Δ ∧ X.On w m ∧ ∀ e, X.Inc w e → z e = if X.lineE e = m then 1 else 0 := by
  rcases zmod2_cases t with rfl | rfl
  · exact .inl fun e he => by rw [hz e he]; simp
  · exact .inr ⟨x, hxΔ, hwx, hz⟩

open Classical in
/-- **A triangle and a fourth line: the bounding direction.** If the triangle cycle
`Pa + Pb + Pc` (segments of three non-concurrent lines between their meeting points) bounds,
the fourth line `Δ`, through none of the three vertices, crosses an even number of its sides. -/
theorem tri_bound (hbf : BigonFree X.On) (hs : X.Straight) {a b c Δ : L}
    {pab pbc pca : X.M.Vtx} (hpab : X.On pab a ∧ X.On pab b) (hpbc : X.On pbc b ∧ X.On pbc c)
    (hpca : X.On pca c ∧ X.On pca a) (hab : a ≠ b) (hnc : ¬X.On pab c)
    (hΔ : ¬X.On pab Δ ∧ ¬X.On pbc Δ ∧ ¬X.On pca Δ) {Pa Pb Pc : X.M.Edge → ZMod 2}
    (sa : ∀ e, Pa e ≠ 0 → X.lineE e = a) (sb : ∀ e, Pb e ≠ 0 → X.lineE e = b)
    (sc : ∀ e, Pc e ≠ 0 → X.lineE e = c)
    (ba : X.incM *ᵥ Pa = Pi.single pab 1 + Pi.single pca 1)
    (bb : X.incM *ᵥ Pb = Pi.single pab 1 + Pi.single pbc 1)
    (bc : X.incM *ᵥ Pc = Pi.single pbc 1 + Pi.single pca 1) {ea eb ec : X.M.Edge}
    (ha : X.lineE ea = a ∧ ∃ w, X.Inc w ea ∧ X.On w Δ)
    (hb : X.lineE eb = b ∧ ∃ w, X.Inc w eb ∧ X.On w Δ)
    (hc : X.lineE ec = c ∧ ∃ w, X.Inc w ec ∧ X.On w Δ) (hz : Pa + Pb + Pc ∈ X.B1) :
    Pa ea + Pb eb + Pc ec = 0 := by
  classical
  obtain ⟨S, hS⟩ := hz
  simp only [Matrix.mulVecLin_apply] at hS
  obtain ⟨hΔ1, hΔ2, hΔ3⟩ := hΔ
  have hac : a ≠ c := fun h => hnc (h ▸ hpab.1)
  have hbc : b ≠ c := fun h => hnc (h ▸ hpab.2)
  have haΔ : a ≠ Δ := fun h => hΔ1 (h ▸ hpab.1)
  have hbΔ : b ≠ Δ := fun h => hΔ1 (h ▸ hpab.2)
  have hcΔ : c ≠ Δ := fun h => hΔ2 (h ▸ hpbc.2)
  obtain ⟨wa, hwa, hwaΔ⟩ := ha.2
  obtain ⟨wb, hwb, hwbΔ⟩ := hb.2
  obtain ⟨wc, hwc, hwcΔ⟩ := hc.2
  have oa : X.On wa a := ha.1 ▸ on_of_inc hwa
  have ob : X.On wb b := hb.1 ▸ on_of_inc hwb
  have oc : X.On wc c := hc.1 ▸ on_of_inc hwc
  have nab : ¬X.On wa b := fun h => hΔ1 (meet_eq hab oa h hpab.1 hpab.2 ▸ hwaΔ)
  have nac : ¬X.On wa c := fun h => hΔ3 (meet_eq hac oa h hpca.2 hpca.1 ▸ hwaΔ)
  have nba : ¬X.On wb a := fun h => hΔ1 (meet_eq hab h ob hpab.1 hpab.2 ▸ hwbΔ)
  have nbc : ¬X.On wb c := fun h => hΔ2 (meet_eq hbc ob h hpbc.1 hpbc.2 ▸ hwbΔ)
  have nca : ¬X.On wc a := fun h => hΔ3 (meet_eq hac h oc hpca.2 hpca.1 ▸ hwcΔ)
  have ncb : ¬X.On wc b := fun h => hΔ2 (meet_eq hbc h oc hpbc.1 hpbc.2 ▸ hwcΔ)
  have ne : ∀ {w v : X.M.Vtx} {l : L}, X.On w l → ¬X.On v l → w ≠ v := fun h h' e => h' (e ▸ h)
  have va : ∀ e, X.Inc wa e → (Pa + Pb + Pc) e = if X.lineE e = a then Pa ea else 0 :=
    fun e he => by
      simp only [Pi.add_apply, off_line sb nab he, off_line sc nac he, add_zero]
      exact seg_val hbf hs sa ba (ne hwaΔ hΔ1) (ne hwaΔ hΔ3) ha.1 hwa e he
  have vb : ∀ e, X.Inc wb e → (Pa + Pb + Pc) e = if X.lineE e = b then Pb eb else 0 :=
    fun e he => by
      simp only [Pi.add_apply, off_line sa nba he, off_line sc nbc he, add_zero, zero_add]
      exact seg_val hbf hs sb bb (ne hwbΔ hΔ1) (ne hwbΔ hΔ2) hb.1 hwb e he
  have vc : ∀ e, X.Inc wc e → (Pa + Pb + Pc) e = if X.lineE e = c then Pc ec else 0 :=
    fun e he => by
      simp only [Pi.add_apply, off_line sa nca he, off_line sb ncb he, zero_add]
      exact seg_val hbf hs sc bc (ne hwcΔ hΔ2) (ne hwcΔ hΔ3) hc.1 hwc e he
  have v0 : ∀ w, ¬X.On w a → ¬X.On w b → ¬X.On w c → ∀ e, X.Inc w e → (Pa + Pb + Pc) e = 0 :=
    fun w h1 h2 h3 e he => by simp [off_line sa h1 he, off_line sb h2 he, off_line sc h3 he]
  have z0 : ∀ {x : L} {P : X.M.Edge → ZMod 2}, (∀ e, P e ≠ 0 → X.lineE e = x) → x ≠ Δ →
      ∀ {e}, X.lineE e = Δ → P e = 0 := fun hP hx e he =>
    by_contra fun h => hx ((hP e h).symm.trans he)
  have key := parity hbf hs S Δ (fun e he => by
      rw [hS, Pi.add_apply, Pi.add_apply, z0 sa haΔ he, z0 sb hbΔ he, z0 sc hcΔ he]; simp)
    (fun w hw => by
      rw [hS]
      by_cases h1 : X.On w a
      · exact cross_of haΔ h1 (meet_eq haΔ h1 hw oa hwaΔ ▸ va)
      by_cases h2 : X.On w b
      · exact cross_of hbΔ h2 (meet_eq hbΔ h2 hw ob hwbΔ ▸ vb)
      by_cases h3 : X.On w c
      · exact cross_of hcΔ h3 (meet_eq hcΔ h3 hw oc hwcΔ ▸ vc)
      exact .inl (v0 w h1 h2 h3))
  rw [hS] at key
  rw [← key, Finset.sum_congr rfl fun w _ => show _ = (if w = wa then Pa ea else 0) +
      (if w = wb then Pb eb else 0) + (if w = wc then Pc ec else 0) from ?_]
  · simp [Finset.sum_add_distrib]
  by_cases h1 : w = wa
  · subst h1; simpa [ne oa nba, ne oa nca] using ind_val hwaΔ va hwa ha.1
  by_cases h2 : w = wb
  · subst h2; simpa [ne ob nab, ne ob ncb] using ind_val hwbΔ vb hwb hb.1
  by_cases h3 : w = wc
  · subst h3; simpa [ne oc nac, ne oc nbc] using ind_val hwcΔ vc hwc hc.1
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, add_zero, add_zero]
  exact ite_eq_right fun ⟨hw, e, he, hz⟩ => hz (v0 w (fun h => h1 (meet_eq haΔ h hw oa hwaΔ))
    (fun h => h2 (meet_eq hbΔ h hw ob hwbΔ)) (fun h => h3 (meet_eq hcΔ h hw oc hwcΔ)) e he)

/-- Exactly one of a cycle `z` and `z + D`, for a line `D`, bounds. -/
theorem flip (hbf : BigonFree X.On) (hs : X.Straight) {a Δ : L} (h : a ≠ Δ)
    {z : X.M.Edge → ZMod 2} (hz : z ∈ X.Z1) : z ∈ X.B1 ↔ z + X.lineChain a ∉ X.B1 :=
  ⟨fun h1 h2 => lineChain_not_mem hbf hs h (by
      have hzz : z + z = 0 := funext fun e => add_self' (z e)
      have := X.B1.add_mem h1 h2
      rwa [← add_assoc, hzz, zero_add] at this),
    fun h1 => (Z1_cases hbf hs h hz).resolve_right h1⟩

open Classical in
/-- **The orientation of a triangle is read on the skeleton** (page 50, condition (A5)).
Let `a, b, c` be three non-concurrent lines meeting at `pab, pbc, pca`, `Pa, Pb, Pc` segments
of `a, b, c` between these points, and `Δ` a fourth line through none of them; let
`ea, eb, ec` be edges of `a, b, c` at their meeting points with `Δ`. The triangle cycle
`Pa + Pb + Pc` bounds a union of faces iff `Δ` crosses an even number of its sides:
`Pa ea + Pb eb + Pc ec = 0`. The right-hand side involves only the skeleton and its lines, so
the canonical orientation of the triangle (which four of its eight cycles bound) is determined
by the skeleton, and does not depend on `Δ`. -/
theorem triangle_iff (hbf : BigonFree X.On) (hs : X.Straight) {a b c Δ : L}
    {pab pbc pca : X.M.Vtx} (hpab : X.On pab a ∧ X.On pab b) (hpbc : X.On pbc b ∧ X.On pbc c)
    (hpca : X.On pca c ∧ X.On pca a) (hab : a ≠ b) (hnc : ¬X.On pab c)
    (hΔ : ¬X.On pab Δ ∧ ¬X.On pbc Δ ∧ ¬X.On pca Δ) {Pa Pb Pc : X.M.Edge → ZMod 2}
    (sa : ∀ e, Pa e ≠ 0 → X.lineE e = a) (sb : ∀ e, Pb e ≠ 0 → X.lineE e = b)
    (sc : ∀ e, Pc e ≠ 0 → X.lineE e = c)
    (ba : X.incM *ᵥ Pa = Pi.single pab 1 + Pi.single pca 1)
    (bb : X.incM *ᵥ Pb = Pi.single pab 1 + Pi.single pbc 1)
    (bc : X.incM *ᵥ Pc = Pi.single pbc 1 + Pi.single pca 1) {ea eb ec : X.M.Edge}
    (ha : X.lineE ea = a ∧ ∃ w, X.Inc w ea ∧ X.On w Δ)
    (hb : X.lineE eb = b ∧ ∃ w, X.Inc w eb ∧ X.On w Δ)
    (hc : X.lineE ec = c ∧ ∃ w, X.Inc w ec ∧ X.On w Δ) :
    Pa + Pb + Pc ∈ X.B1 ↔ Pa ea + Pb eb + Pc ec = 0 := by
  refine ⟨tri_bound hbf hs hpab hpbc hpca hab hnc hΔ sa sb sc ba bb bc ha hb hc, fun h0 => ?_⟩
  have hz : Pa + Pb + Pc ∈ X.Z1 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add, ba, bb, bc]
    exact funext fun v => (by decide : ∀ p q r : ZMod 2, p + r + (p + q) + (q + r) = 0) _ _ _
  by_contra hn
  have hl := (flip hbf hs (show a ≠ Δ from fun h => hΔ.1 (h ▸ hpab.1)) hz).not.1 hn
  rw [not_not, add_right_comm, add_right_comm Pa] at hl
  have := tri_bound hbf hs hpab hpbc hpca hab hnc hΔ (Pa := Pa + X.lineChain a)
    (fun e he => by_contra fun h => he (by simp [lineChain, h, by_contra fun h' => h (sa e h')]))
    sb sc (by rw [Matrix.mulVec_add, ba, show X.incM *ᵥ X.lineChain a = 0 from
      lineChain_mem hbf hs a, add_zero]) bb bc ha hb hc hl
  rw [Pi.add_apply, show X.lineChain a ea = 1 by simp [lineChain, ha.1]] at this
  exact one_ne_zero (by linear_combination this - h0 : (1 : ZMod 2) = 0)

end Parity

/-! ### Lifting isomorphisms of skeletons (page 41) -/

section Lift

/-- Two edge-ends adjacent around a vertex lie on different lines. -/
theorem line_a1_ne (hs : X.Straight) (d : D) : X.line (X.M.a1 d) ≠ X.line d := by
  classical
  obtain ⟨e, he, hl⟩ := X.two d
  have h2 : 1 < X.nu (X.M.vtx d) := Finset.one_lt_card.2 ⟨_, Finset.mem_image.2 ⟨d, by simp, rfl⟩,
    _, Finset.mem_image.2 ⟨e, by simp [he], rfl⟩, Ne.symm hl⟩
  exact fun h => line_inj hs d zero_lt_one h2 (by simpa [phi_apply, X.line_a2] using h.symm)

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

/-- A flag is determined by its vertex, its edge and the edge after it. -/
theorem dart_unique (hbf : BigonFree X.On) {y y' : D} (hv : X.M.vtx y' = X.M.vtx y)
    (he : X.M.edge y' = X.M.edge y) (h1 : X.M.edge (X.M.a1 y') = X.M.edge (X.M.a1 y)) :
    y' = y := by
  rcases (at_edge hbf).1 ⟨hv, he⟩ with h | rfl
  · exact h
  · exact (edge_a1_a2_ne hbf y h1).elim

omit [Fintype D'] in
theorem exists_dart (hbf : BigonFree X.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) (d : D) :
    ∃ d', X'.M.vtx d' = f.fV (X.M.vtx d) ∧ X'.M.edge d' = f.fE (X.M.edge d) ∧
      X'.M.edge (X'.M.a1 d') = f.fE (X.M.edge (X.M.a1 d)) ∧
      X'.M.edge (X'.M.a1 (X'.M.a0 d')) = f.fE (X.M.edge (X.M.a1 (X.M.a0 d))) := by
  obtain ⟨d', h1, h2, h3⟩ := hT _ _ _ ⟨d, rfl, rfl, rfl⟩
  refine ⟨d', ?_, h2, h1, h3⟩
  have iv := (f.inc _ _).1 (⟨d, rfl, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge d))
  have iw := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
  rw [← h2, inc_iff] at iv iw
  have hvw : f.fV (X.M.vtx d) ≠ f.fV (X.M.vtx (X.M.a0 d)) := fun h => noLoop hbf d (f.fV.injective h).symm
  by_contra hne
  have hw : X'.M.vtx d' = f.fV (X.M.vtx (X.M.a0 d)) :=
    (iw.resolve_right fun h' => hvw ((iv.resolve_left fun h => hne h.symm).trans h'.symm)).symm
  -- the edge after `d` would join both ends of `d`, on another line
  have : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge (X.M.a1 d)) := by
    rw [f.inc, ← h1, ← hw]; exact ⟨_, vtx_a1 d', rfl⟩
  exact noLoop hbf d (meet_eq (line_a1_ne hs d) (lineE_edge (X := X) (X.M.a1 d) ▸ on_of_inc this)
    ⟨_, rfl, X.line_a0 d⟩ ⟨_, vtx_a1 d, rfl⟩ ⟨d, rfl, rfl⟩)

/-- **The general theorem on maps, page 41.** An isomorphism of decomposed skeletons that
carries the three-edge face paths to face paths is induced by a morphism of the arrangements
(commuting with `a0, a1, a2`, over the given bijections). -/
theorem lift (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) :
    ∃ g : D → D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      (∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ∧ ∀ d, X'.line (g d) = f.fL (X.line d) := by
  choose g hv he h1 h3 using exists_dart hbf hs f hT
  have hv' : ∀ d, X'.M.vtx (X'.M.a0 (g d)) = f.fV (X.M.vtx (X.M.a0 d)) := fun d => by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
    rw [← he, inc_iff] at this
    exact (this.resolve_left fun h => noLoop hbf d (f.fV.injective (h.trans (hv d)))).symm
  refine ⟨g, fun d => ?_, fun d => ?_, fun d => ?_, hv, he, fun d => ?_⟩
  · exact dart_unique hbf' (by rw [hv, hv']) (by simp [he]) (by rw [h1, h3])
  · exact dart_unique hbf' (by simp [hv]) (by rw [he, h1]) (by rw [h1, X.M.a1_a1, X'.M.a1_a1, he])
  · exact ((at_edge hbf').1 (⟨by simp [hv], by simp [he]⟩ :
      X'.M.vtx (g (X.M.a2 d)) = X'.M.vtx (g d) ∧ X'.M.edge (g (X.M.a2 d)) = X'.M.edge (g d))
      ).resolve_left fun h => edge_a1_a2_ne hbf d (f.fE.injective (by rw [← h1, ← h1, h]))
  · rw [← lineE_edge, he, f.line]; rfl

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
  constructor
  · rintro ⟨g, g0, g1, -, -, ge⟩ e1 e e2
    constructor
    · rintro ⟨d, rfl, rfl, rfl⟩
      exact ⟨g d, by rw [← g1, ge], ge d, by rw [← g0, ← g1, ge]⟩
    · rintro ⟨d', h1, h2, h3⟩
      refine ⟨g.symm d', ?_, ?_, ?_⟩ <;> apply f.fE.injective <;> simp [← ge, g0, g1, h1, h2, h3]
  · intro hT
    obtain ⟨g, g0, g1, g2, gv, ge, -⟩ := lift hbf hbf' hs f fun _ _ _ => (hT _ _ _).1
    obtain ⟨g', -, g1', -, gv', ge', -⟩ := lift hbf' hbf hs' f.symm fun e1 e e2 h =>
      (hT _ _ _).2 (by simpa [SkelIso.symm] using h)
    have l : g' ∘ g = id := faithful hbf (fun d => by simp [g1, g1']) (fun _ => rfl)
      (fun d => by simp [gv, gv', SkelIso.symm]) (fun d => by simp [ge, ge', SkelIso.symm])
    have r : g ∘ g' = id := faithful hbf' (fun d => by simp [g1, g1']) (fun _ => rfl)
      (fun d => by simp [gv, gv', SkelIso.symm]) (fun d => by simp [ge, ge', SkelIso.symm])
    exact ⟨⟨g, g', congrFun l, congrFun r⟩, g0, g1, g2, gv, ge⟩

end Lift

/-! ### Segments of a line are read on the skeleton -/

section Segments

open Matrix

open Classical in
/-- **A cycle carried by one line is `0` or the whole line.** -/
theorem line_cycle (hbf : BigonFree X.On) (hs : X.Straight) {l : L} {z : X.M.Edge → ZMod 2}
    (hz : z ∈ X.Z1) (hl : ∀ e, z e ≠ 0 → X.lineE e = l) : z = 0 ∨ z = X.lineChain l := by
  have hw : ∀ x, X.line x = l →
      z (X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x)) = z (X.M.edge x) := fun x hx => by
    have h0 := congrFun (LinearMap.mem_ker.1 hz) (X.M.vtx x)
    simp only [Matrix.mulVecLin_apply, Pi.zero_apply] at h0
    rw [incM_mulVec, Finset.sum_congr rfl
      (g := fun e => if X.Inc (X.M.vtx x) e ∧ X.lineE e = X.line x then z e else 0) fun e _ => by
        by_cases h1 : X.Inc (X.M.vtx x) e <;> by_cases h2 : X.lineE e = X.line x <;> simp [h1, h2]
        exact by_contra fun h => h2 (hx ▸ hl e h), ← Finset.sum_filter, (line_edges hbf hs x).1,
      Finset.sum_pair (line_edges hbf hs x).2] at h0
    exact (two_eq _ _ h0).symm
  have step : ∀ x y, X.M.vtx y = X.M.vtx x → X.line y = X.line x → X.line x = l →
      z (X.M.edge y) = z (X.M.edge x) := fun x y hv hly hx => by
    have : X.M.edge y ∈ Finset.univ.filter fun e => X.Inc (X.M.vtx x) e ∧ X.lineE e = X.line x :=
      by simpa [hly] using ⟨y, hv, rfl⟩
    rw [(line_edges hbf hs x).1] at this
    rcases Finset.mem_insert.1 this with h | h
    · rw [h]
    · rw [Finset.mem_singleton.1 h, hw x hx]
  have const : ∀ d e, X.line d = l → X.line e = l → z (X.M.edge e) = z (X.M.edge d) :=
    fun d e hd he => (eqvGen_iff (fun x => X.line x = l → z (X.M.edge x) = z (X.M.edge d))
      (by
        rintro x y (rfl | ⟨h1, h2⟩)
        · simp [X.line_a0]
        · exact ⟨fun h hl' => (step x y h1 h2 (h2.symm.trans hl')).trans (h (h2.symm.trans hl')),
            fun h hl' => (step x y h1 h2 hl').symm.trans (h (h2.trans hl'))⟩)
      (X.conn d e (hd.trans he.symm))).1 (fun _ => rfl) he
  by_cases h0 : ∃ d, X.line d = l
  · obtain ⟨d0, hd0⟩ := h0
    rcases zmod2_cases (z (X.M.edge d0)) with h | h
    · refine .inl (funext fun e => ?_)
      obtain ⟨d, rfl⟩ := edge_surj e
      exact by_contra fun hne => hne (by rw [const d0 d hd0 (hl _ hne), h]; rfl)
    · refine .inr (funext fun e => ?_)
      obtain ⟨d, rfl⟩ := edge_surj e
      simp only [lineChain]
      split_ifs with hd
      · rw [const d0 d hd0 hd, h]
      · exact by_contra fun hne => hd (hl _ hne)
  · exact .inl (funext fun e => by
      obtain ⟨d, rfl⟩ := edge_surj e
      exact by_contra fun hne => h0 ⟨d, hl _ hne⟩)

open Classical in
/-- **Segments are read on the skeleton.** Two chains carried by a line `l` with the same
boundary (for instance two segments of `l` with the same ends) are equal or complementary in
`l`; so a segment is determined by its ends and any one of its edges. -/
theorem seg_unique (hbf : BigonFree X.On) (hs : X.Straight) {l : L} {P P' : X.M.Edge → ZMod 2}
    (hP : ∀ e, P e ≠ 0 → X.lineE e = l) (hP' : ∀ e, P' e ≠ 0 → X.lineE e = l)
    (h : X.incM *ᵥ P = X.incM *ᵥ P') : P' = P ∨ P' = P + X.lineChain l := by
  have hz : P + P' ∈ X.Z1 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add, h]
    exact funext fun v => add_self' _
  rcases line_cycle hbf hs hz fun e he => by_contra fun h' => he (by
      simp [by_contra fun h => h' (hP e h), by_contra fun h => h' (hP' e h)]) with h0 | h0
  · exact .inl (funext fun e => (two_eq _ _ (congrFun h0 e)).symm)
  · refine .inr (funext fun e => ?_)
    rw [Pi.add_apply, ← h0, Pi.add_apply, ← add_assoc, add_self', zero_add]

end Segments

/-! ### Transport of triangle orientations along a skeleton isomorphism -/

section Transport

open Matrix

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

omit [Fintype D] in
/-- A line passes through a vertex iff one of its edges ends there: `On` is read on the
skeleton. -/
theorem on_iff {v : X.M.Vtx} {l : L} : X.On v l ↔ ∃ e, X.Inc v e ∧ X.lineE e = l :=
  ⟨fun ⟨d, hd, hl⟩ => ⟨X.M.edge d, ⟨d, hd, rfl⟩, hl⟩, fun ⟨_, h, hl⟩ => hl ▸ on_of_inc h⟩

namespace SkelIso

variable (f : SkelIso X X')

omit [Fintype D] [Fintype D'] in
theorem on_map {v : X.M.Vtx} {l : L} : X.On v l ↔ X'.On (f.fV v) (f.fL l) := by
  simp only [on_iff]
  constructor
  · rintro ⟨e, h, rfl⟩; exact ⟨f.fE e, (f.inc _ _).1 h, f.line e⟩
  · rintro ⟨e', h, hl⟩
    refine ⟨f.fE.symm e', (f.inc _ _).2 (by simpa using h), f.fL.injective ?_⟩
    rw [← f.line]; simpa using hl

/-- The image of a chain of edges. -/
def mapC (c : X.M.Edge → ZMod 2) : X'.M.Edge → ZMod 2 := c ∘ f.fE.symm

omit [Fintype D] [Fintype D'] in
@[simp] theorem mapC_apply (c : X.M.Edge → ZMod 2) (e : X.M.Edge) : f.mapC c (f.fE e) = c e := by
  simp [mapC]

omit [Fintype D] [Fintype D'] in
theorem supp_map {c : X.M.Edge → ZMod 2} {a : L} (h : ∀ e, c e ≠ 0 → X.lineE e = a) (e' : X'.M.Edge)
    (h' : f.mapC c e' ≠ 0) : X'.lineE e' = f.fL a := by
  obtain ⟨e, rfl⟩ := f.fE.surjective e'
  rw [f.line, h e (by rwa [mapC_apply] at h')]

open Classical in
theorem bd_map {c : X.M.Edge → ZMod 2} {p q : X.M.Vtx}
    (h : X.incM *ᵥ c = Pi.single p 1 + Pi.single q 1) :
    X'.incM *ᵥ f.mapC c = Pi.single (f.fV p) 1 + Pi.single (f.fV q) 1 := by
  funext v'
  obtain ⟨v, rfl⟩ := f.fV.surjective v'
  have := congrFun h v
  rw [incM_mulVec] at this ⊢
  rw [← f.fE.sum_comp]
  simp only [mapC_apply, ← f.inc]
  simpa [Pi.single_apply] using this

omit [Fintype D] [Fintype D'] in
theorem meets_map {e : X.M.Edge} {a Δ : L} (h : X.lineE e = a ∧ ∃ w, X.Inc w e ∧ X.On w Δ) :
    X'.lineE (f.fE e) = f.fL a ∧ ∃ w, X'.Inc w (f.fE e) ∧ X'.On w (f.fL Δ) := by
  obtain ⟨rfl, w, h1, h2⟩ := h
  exact ⟨f.line e, f.fV w, (f.inc _ _).1 h1, f.on_map.1 h2⟩

open Classical in
/-- **Skeleton isomorphisms preserve the orientation of triangles** ((A5) transported). For a
triangle of three non-concurrent lines with a fourth line through none of its vertices, a
triangle cycle bounds a union of faces iff its image by a skeleton isomorphism does. -/
theorem triangle_map (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) {a b c Δ : L}
    {pab pbc pca : X.M.Vtx} (hpab : X.On pab a ∧ X.On pab b) (hpbc : X.On pbc b ∧ X.On pbc c)
    (hpca : X.On pca c ∧ X.On pca a) (hab : a ≠ b) (hnc : ¬X.On pab c)
    (hΔ : ¬X.On pab Δ ∧ ¬X.On pbc Δ ∧ ¬X.On pca Δ) {Pa Pb Pc : X.M.Edge → ZMod 2}
    (sa : ∀ e, Pa e ≠ 0 → X.lineE e = a) (sb : ∀ e, Pb e ≠ 0 → X.lineE e = b)
    (sc : ∀ e, Pc e ≠ 0 → X.lineE e = c)
    (ba : X.incM *ᵥ Pa = Pi.single pab 1 + Pi.single pca 1)
    (bb : X.incM *ᵥ Pb = Pi.single pab 1 + Pi.single pbc 1)
    (bc : X.incM *ᵥ Pc = Pi.single pbc 1 + Pi.single pca 1) {ea eb ec : X.M.Edge}
    (ha : X.lineE ea = a ∧ ∃ w, X.Inc w ea ∧ X.On w Δ)
    (hb : X.lineE eb = b ∧ ∃ w, X.Inc w eb ∧ X.On w Δ)
    (hc : X.lineE ec = c ∧ ∃ w, X.Inc w ec ∧ X.On w Δ) :
    Pa + Pb + Pc ∈ X.B1 ↔ f.mapC Pa + f.mapC Pb + f.mapC Pc ∈ X'.B1 := by
  have o := fun {v} {l} => f.on_map (v := v) (l := l)
  rw [triangle_iff hbf hs hpab hpbc hpca hab hnc hΔ sa sb sc ba bb bc ha hb hc,
    triangle_iff hbf' hs' ⟨o.1 hpab.1, o.1 hpab.2⟩ ⟨o.1 hpbc.1, o.1 hpbc.2⟩
      ⟨o.1 hpca.1, o.1 hpca.2⟩ (f.fL.injective.ne hab) (o.not.1 hnc)
      ⟨o.not.1 hΔ.1, o.not.1 hΔ.2.1, o.not.1 hΔ.2.2⟩ (f.supp_map sa) (f.supp_map sb)
      (f.supp_map sc) (f.bd_map ba) (f.bd_map bb) (f.bd_map bc) (f.meets_map ha)
      (f.meets_map hb) (f.meets_map hc), mapC_apply, mapC_apply, mapC_apply]

end SkelIso

end Transport

/-! ### The triangle of a face path bounds (Jordan for the triangles of page 50) -/

section FacePath

open Matrix

/-- Half a turn after `y` meets the edges of the line `a1 y` once: a chain on that line which
is `1` at the edge after `y` has sum `1` there. -/
theorem half_one (hs : X.Straight) (y : D) {l : L} {P : X.M.Edge → ZMod 2}
    (hP : ∀ e, P e ≠ 0 → X.lineE e = l) (hl : X.line (X.M.a1 y) = l)
    (h1 : P (X.M.edge (X.M.a1 y)) = 1) :
    ∑ i ∈ Finset.range (X.nu (X.M.vtx y)), P (X.M.edge ((X.phi ^ (i + 1)) y)) = 1 := by
  classical
  have hν : 0 < X.nu (X.M.vtx y) := Finset.card_pos.2 ⟨X.line y, Finset.mem_image.2 ⟨y, by simp, rfl⟩⟩
  rw [Finset.sum_eq_single 0]
  · simpa [phi_apply] using h1
  · intro i hi hi0
    refine by_contra fun h => line_inj hs (X.phi y) (Nat.pos_of_ne_zero hi0) (by simpa using hi) ?_
    rw [pow_zero, Equiv.Perm.one_apply, phi_apply, X.line_a2, hl, ← hP _ h, lineE_edge, pow_succ,
      Equiv.Perm.mul_apply]
    rfl
  · exact fun h => absurd (Finset.mem_range.2 hν) h

/-- A chain on a line missing the vertex of `y` vanishes on the half turn after `y`. -/
theorem half_zero (y : D) {l : L} {P : X.M.Edge → ZMod 2} (hP : ∀ e, P e ≠ 0 → X.lineE e = l)
    (hy : ¬X.On (X.M.vtx y) l) :
    ∑ i ∈ Finset.range (X.nu (X.M.vtx y)), P (X.M.edge ((X.phi ^ (i + 1)) y)) = 0 :=
  Finset.sum_eq_zero fun _ _ => off_line hP hy ⟨_, vtx_phi' _ _, rfl⟩

open Classical in
/-- The half turn after `y` does not come back to the edge of `y`. -/
theorem half_edge (hbf : BigonFree X.On) (y : D) :
    ∑ i ∈ Finset.range (X.nu (X.M.vtx y)),
      (Pi.single (X.M.edge y) 1 : X.M.Edge → ZMod 2) (X.M.edge ((X.phi ^ (i + 1)) y)) = 0 := by
  refine Finset.sum_eq_zero fun i hi => Pi.single_eq_of_ne (fun h => ?_) _
  have hi := Finset.mem_range.1 hi
  rcases (at_edge hbf).1 ⟨vtx_phi' _ _, h⟩ with h | h
  · exact pow_ne (X := X) y (Nat.succ_pos i) (by omega) (by simpa using h.symm)
  · exact a2_ne_pow 0 (i + 1) y (by simpa using h.symm)

open Classical in
/-- **The parity lemma along a line, across one edge.** Let `z = ∂S` vanish on the edges of the
line `m` of `d` other than `e = edge d`, and at the vertices of `m` other than the ends of `e`.
Then the half turns after `d` and after `a0 d` (on the same side of `e`) meet `z` an even
number of times in all. -/
theorem edge_parity (hbf : BigonFree X.On) (hs : X.Straight) (S : X.M.Face → ZMod 2) (d : D)
    (h1 : ∀ ε, X.lineE ε = X.line d → ε ≠ X.M.edge d → (X.bdM *ᵥ S) ε = 0)
    (h0 : ∀ q, X.On q (X.line d) → q ≠ X.M.vtx d → q ≠ X.M.vtx (X.M.a0 d) →
      ∀ ε, X.Inc q ε → (X.bdM *ᵥ S) ε = 0) :
    ∑ i ∈ Finset.range (X.nu (X.M.vtx d)), (X.bdM *ᵥ S) (X.M.edge ((X.phi ^ (i + 1)) d)) +
      ∑ i ∈ Finset.range (X.nu (X.M.vtx (X.M.a0 d))),
        (X.bdM *ᵥ S) (X.M.edge ((X.phi ^ (i + 1)) (X.M.a0 d))) = 0 := by
  set Δ := X.line d
  let μ : X.M.Edge → ZMod 2 := fun ε => if ε = X.M.edge d then S (X.M.face d) else S (X.M.face ε.out)
  have hμ : ∀ y, X.line y = Δ → (X.M.edge y ≠ X.M.edge d ∨ y = d ∨ y = X.M.a0 d) →
      μ (X.M.edge y) = S (X.M.face y) := by
    rintro y hy (hne | rfl | rfl)
    · have h0' : S (X.M.face (X.M.a2 y)) = S (X.M.face y) :=
        two_eq _ _ (by rw [add_comm, ← bd_apply]; exact h1 _ hy hne)
      simp only [μ, hne, ite_false]
      rcases edge_eq.1 (Quot.out_eq (X.M.edge y)) with h | h | h | h <;> simp [h, h0']
    · simp [μ]
    · simp [μ]
  have loc : ∀ x, X.line x = Δ → μ (X.M.edge x) = S (X.M.face x) →
      μ (X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x)) = S (X.M.face ((X.phi ^ X.nu (X.M.vtx x)) x)) →
      ∑ ε, (if X.Inc (X.M.vtx x) ε ∧ X.lineE ε = Δ then μ ε else 0) =
        ∑ i ∈ Finset.range (X.nu (X.M.vtx x)), (X.bdM *ᵥ S) (X.M.edge ((X.phi ^ (i + 1)) x)) := by
    intro x hx m1 m2
    obtain ⟨hfil, hee⟩ := line_edges hbf hs x
    rw [hx] at hfil
    rw [← Finset.sum_filter, hfil, Finset.sum_pair hee, m1, m2, face_phi_pow S, ← add_assoc,
      add_self', zero_add]
  have glob : ∑ q, ∑ ε, (if X.Inc q ε ∧ X.lineE ε = Δ then μ ε else 0) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ε _ => ?_
    obtain ⟨y, rfl⟩ := edge_surj ε
    simp only [ite_and]
    rw [sum_inc hbf y (fun _ => if X.lineE (X.M.edge y) = Δ then μ (X.M.edge y) else 0), add_self']
  rw [Fintype.sum_eq_add (X.M.vtx d) (X.M.vtx (X.M.a0 d)) (noLoop hbf d).symm] at glob
  · rwa [loc d rfl (hμ d rfl (.inr (.inl rfl))) (hμ _ (hs d) (.inl (line_edges hbf hs d).2.symm)),
      loc (X.M.a0 d) (X.line_a0 d) (hμ _ (X.line_a0 d) (.inr (.inr rfl)))
        (hμ _ ((hs _).trans (X.line_a0 d)) (.inl (by simpa using (line_edges hbf hs (X.M.a0 d)).2.symm)))] at glob
  · rintro q ⟨hqv, hqw⟩
    by_cases hq : X.On q Δ
    · obtain ⟨x, rfl, hx⟩ := hq
      have far : ∀ y, X.M.vtx y = X.M.vtx x → X.M.edge y ≠ X.M.edge d := fun y hy h => by
        rcases (inc_iff d (X.M.vtx x)).1 (h ▸ ⟨y, hy, rfl⟩) with h' | h'
        exacts [hqv h', hqw h']
      rw [loc x hx (hμ x hx (.inl (far x rfl))) (hμ _ ((hs x).trans hx) (.inl (far _ (by simp))))]
      exact Finset.sum_eq_zero fun i _ => h0 _ ⟨x, rfl, hx⟩ hqv hqw _ ⟨_, by simp, rfl⟩
    · exact Finset.sum_eq_zero fun ε _ => ite_eq_right fun ⟨h1, h2⟩ => hq (h2 ▸ on_of_inc h1)

open Classical in
/-- The boundary of an edge is its two ends. -/
theorem bd_single (hbf : BigonFree X.On) (d : D) :
    X.incM *ᵥ (Pi.single (X.M.edge d) 1 : X.M.Edge → ZMod 2) =
      Pi.single (X.M.vtx d) 1 + Pi.single (X.M.vtx (X.M.a0 d)) 1 := by
  have hvw := noLoop hbf d
  funext v
  simp only [Matrix.mulVec_single, incM]
  by_cases h1 : v = X.M.vtx d
  · subst h1; simp [hvw.symm, show X.Inc (X.M.vtx d) (X.M.edge d) from ⟨d, rfl, rfl⟩]
  by_cases h2 : v = X.M.vtx (X.M.a0 d)
  · subst h2; simp [hvw, show X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d) from ⟨_, rfl, edge_a0 d⟩]
  have hn : ¬X.Inc v (X.M.edge d) := fun h => ((inc_iff d v).1 h).elim h1 h2
  simp [h1, h2, hn]

open Classical in
/-- **The triangle of a face path bounds** (Jordan's theorem for the triangles of page 50). Let
`a1 d, d, a1 a0 d` be the flags of a face path `e1, e, e2` (`e = edge d` joining `v` to `w`),
and `Pa`, `Pb` segments of the lines of `e1` and `e2` from `v` and `w` to a common vertex `p`,
starting with `e1` and `e2`. Then the triangle cycle `e + Pa + Pb` bounds a union of faces. -/
theorem path_bounds (hbf : BigonFree X.On) (hs : X.Straight) (d : D) {p : X.M.Vtx}
    {Pa Pb : X.M.Edge → ZMod 2} (sa : ∀ e, Pa e ≠ 0 → X.lineE e = X.line (X.M.a1 d))
    (sb : ∀ e, Pb e ≠ 0 → X.lineE e = X.line (X.M.a1 (X.M.a0 d)))
    (ba : X.incM *ᵥ Pa = Pi.single (X.M.vtx d) 1 + Pi.single p 1)
    (bb : X.incM *ᵥ Pb = Pi.single (X.M.vtx (X.M.a0 d)) 1 + Pi.single p 1)
    (ha : Pa (X.M.edge (X.M.a1 d)) = 1) (hb : Pb (X.M.edge (X.M.a1 (X.M.a0 d))) = 1) :
    Pi.single (X.M.edge d) 1 + Pa + Pb ∈ X.B1 := by
  set a := X.line (X.M.a1 d)
  set b := X.line (X.M.a1 (X.M.a0 d))
  have ham : a ≠ X.line d := line_a1_ne hs d
  have hbm : b ≠ X.line d := by have := line_a1_ne hs (X.M.a0 d); rwa [X.line_a0] at this
  have hvw := noLoop hbf d
  have va : X.On (X.M.vtx d) a := ⟨X.M.a1 d, vtx_a1 d, rfl⟩
  have vm : X.On (X.M.vtx d) (X.line d) := ⟨d, rfl, rfl⟩
  have wb : X.On (X.M.vtx (X.M.a0 d)) b := ⟨_, vtx_a1 _, rfl⟩
  have wm : X.On (X.M.vtx (X.M.a0 d)) (X.line d) := ⟨_, rfl, X.line_a0 d⟩
  have nwa : ¬X.On (X.M.vtx (X.M.a0 d)) a := fun h => hvw (meet_eq ham h wm va vm)
  have nvb : ¬X.On (X.M.vtx d) b := fun h => hvw (meet_eq hbm wb wm h vm)
  have sc : ∀ e, X.lineChain a e ≠ 0 → X.lineE e = a := fun e h => by_contra fun h' => h (by
    simp [lineChain, h'])
  have p0 : ∀ {P : X.M.Edge → ZMod 2} {l}, (∀ e, P e ≠ 0 → X.lineE e = l) → ∀ {ε},
      X.lineE ε ≠ l → P ε = 0 := fun hP ε h => by_contra fun h' => h (hP ε h')
  have he := bd_single hbf d
  have hz : Pi.single (X.M.edge d) 1 + Pa + Pb ∈ X.Z1 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add, he, ba, bb]
    exact funext fun v => (by decide : ∀ x y q : ZMod 2, x + y + (x + q) + (y + q) = 0) _ _ _
  rw [flip hbf hs ham hz]
  rintro ⟨S, hS⟩
  simp only [Matrix.mulVecLin_apply] at hS
  have key := edge_parity hbf hs S d (fun ε hε hne => by
      rw [hS, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hne,
        p0 sa fun h => ham (h.symm.trans hε), p0 sb fun h => hbm (h.symm.trans hε),
        p0 sc fun h => ham (h.symm.trans hε)]
      simp)
    fun q hq hqv hqw ε hε => by
      have hqa : ¬X.On q a := fun h => hqv (meet_eq ham h hq va vm)
      have hqb : ¬X.On q b := fun h => hqw (meet_eq hbm h hq wb wm)
      rw [hS, Pi.add_apply, Pi.add_apply, Pi.add_apply, off_line sa hqa hε, off_line sb hqb hε,
        off_line sc hqa hε, Pi.single_eq_of_ne fun h => by
          rcases (inc_iff d q).1 (h ▸ hε) with h' | h'
          exacts [hqv h', hqw h']]
      simp
  rw [hS] at key
  simp only [Pi.add_apply, Finset.sum_add_distrib] at key
  have e2 := half_edge hbf (X.M.a0 d)
  rw [edge_a0] at e2
  rw [half_edge hbf d, e2, half_one hs d sa rfl ha, half_zero d sb nvb,
    half_one hs d sc rfl (by simp [lineChain, a]), half_zero _ sa nwa,
    half_one hs (X.M.a0 d) sb rfl hb, half_zero _ sc nwa] at key
  exact absurd key (by decide)

end FacePath

/-! ### Simple arrangements: the skeleton functor is full -/

section Simple

open Matrix

open Classical in
/-- **Segments exist**, and can be made to start with any given edge of the line. -/
theorem seg_start (hbf : BigonFree X.On) (hs : X.Straight) {l : L} {v p : X.M.Vtx}
    (hv : X.On v l) (hp : X.On p l) {e1 : X.M.Edge} (he1 : X.lineE e1 = l) :
    ∃ P : X.M.Edge → ZMod 2, (∀ e, P e ≠ 0 → X.lineE e = l) ∧
      X.incM *ᵥ P = Pi.single v 1 + Pi.single p 1 ∧ P e1 = 1 := by
  obtain ⟨x0, rfl, hx0⟩ := hv
  obtain ⟨y, rfl, hy⟩ := hp
  obtain ⟨P, hP, hb⟩ : ∃ P : X.M.Edge → ZMod 2, (∀ e, P e ≠ 0 → X.lineE e = l) ∧
      X.incM *ᵥ P = Pi.single (X.M.vtx x0) 1 + Pi.single (X.M.vtx y) 1 := by
    refine confine (l := l) (fun q => ∃ P : X.M.Edge → ZMod 2, (∀ e, P e ≠ 0 → X.lineE e = l) ∧
      X.incM *ᵥ P = Pi.single (X.M.vtx x0) 1 + Pi.single q 1) ?_ hx0
      ⟨0, by simp, funext fun _ => by simp [add_self']⟩ hy
    rintro x hx ⟨P, hP, hb⟩
    refine ⟨P + Pi.single (X.M.edge x) 1, fun e he => ?_, ?_⟩
    · by_cases h : e = X.M.edge x
      · rw [h, lineE_edge, hx]
      · exact hP e (by simpa [Pi.single_eq_of_ne h] using he)
    · rw [Matrix.mulVec_add, hb, bd_single hbf]
      exact funext fun _ => (by decide : ∀ a b c : ZMod 2, a + b + (b + c) = a + c) _ _ _
  rcases zmod2_cases (P e1) with h | h
  · refine ⟨P + X.lineChain l, fun e he => by_contra fun h' => he ?_, ?_, ?_⟩
    · simp [by_contra fun h'' => h' (hP e h''), lineChain, h']
    · rw [Matrix.mulVec_add, hb, show X.incM *ᵥ X.lineChain l = 0 from lineChain_mem hbf hs l,
        add_zero]
    · simp [h, lineChain, he1]
  · exact ⟨P, hP, hb, h⟩

open Classical in
/-- At a vertex of two lines, a line through it other than that of `y` is that of `a1 y`. -/
theorem two_lines (hs : X.Straight) {y : D} (hν : X.nu (X.M.vtx y) = 2) {l : L}
    (hl : X.On (X.M.vtx y) l) (hne : l ≠ X.line y) : l = X.line (X.M.a1 y) := by
  by_contra h
  obtain ⟨x, hx, rfl⟩ := hl
  have : 2 < X.nu (X.M.vtx y) := Finset.two_lt_card_iff.2 ⟨X.line y, X.line (X.M.a1 y), X.line x,
    Finset.mem_image.2 ⟨y, by simp, rfl⟩, Finset.mem_image.2 ⟨_, by simp, rfl⟩,
    Finset.mem_image.2 ⟨x, by simp [hx], rfl⟩, (line_a1_ne hs y).symm, hne.symm, fun e => h e.symm⟩
  omega

/-- **Corners at a vertex of two lines** ((A1)–(A3) in the simple case): the edges of the other
line at the vertex of `y` are the edges after `y` and after `a2 y`. -/
theorem corner2 (hbf : BigonFree X.On) (hs : X.Straight) {y : D} (hν : X.nu (X.M.vtx y) = 2)
    {ε : X.M.Edge} (hε : X.Inc (X.M.vtx y) ε) (hl : X.lineE ε ≠ X.line y) :
    ε = X.M.edge (X.M.a1 y) ∨ ε = X.M.edge (X.M.a1 (X.M.a2 y)) := by
  classical
  have l2 : X.line (X.M.a1 (X.M.a2 y)) = X.line (X.M.a1 y) := two_lines hs hν ⟨_, by simp, rfl⟩
    (by have := line_a1_ne hs (X.M.a2 y); rwa [X.line_a2] at this)
  obtain ⟨hfil, -⟩ := line_edges hbf hs (X.M.a1 y)
  have m : ∀ ζ, X.Inc (X.M.vtx y) ζ → X.lineE ζ = X.line (X.M.a1 y) → ζ = X.M.edge (X.M.a1 y) ∨
      ζ = X.M.edge ((X.phi ^ X.nu (X.M.vtx (X.M.a1 y))) (X.M.a1 y)) := fun ζ h1 h2 => by
    have : ζ ∈ Finset.univ.filter fun e =>
        X.Inc (X.M.vtx (X.M.a1 y)) e ∧ X.lineE e = X.line (X.M.a1 y) := by simp [h1, h2]
    rw [hfil] at this; simpa using this
  rcases m ε hε (two_lines hs hν (on_of_inc hε) hl) with h | h
  · exact .inl h
  rcases m _ ⟨X.M.a1 (X.M.a2 y), by simp, rfl⟩ l2 with h' | h'
  · exact (edge_a1_a2_ne hbf y h').elim
  · exact .inr (h.trans h'.symm)

open Classical in
/-- At the end `vtx y` of a segment on the line of `a1 y`, through a vertex of two lines, the
segment takes the value `1` on exactly one of the two edges of its line. -/
theorem seg_end2 (hbf : BigonFree X.On) (hs : X.Straight) {y : D} (hν : X.nu (X.M.vtx y) = 2)
    {P : X.M.Edge → ZMod 2} {p : X.M.Vtx} (hP : ∀ e, P e ≠ 0 → X.lineE e = X.line (X.M.a1 y))
    (hb : X.incM *ᵥ P = Pi.single (X.M.vtx y) 1 + Pi.single p 1) (hp : p ≠ X.M.vtx y) :
    P (X.M.edge (X.M.a1 y)) + P (X.M.edge (X.M.a1 (X.M.a2 y))) = 1 := by
  have h0 := congrFun hb (X.M.vtx y)
  rw [incM_mulVec, Fintype.sum_eq_add _ _ (edge_a1_a2_ne hbf y).symm fun ζ ⟨h1, h2⟩ => by
    rw [ite_eq_right_iff]
    intro hζ
    by_contra h
    exact (corner2 hbf hs hν hζ (by rw [hP ζ h]; exact line_a1_ne hs y)).elim h1 h2] at h0
  simpa [Pi.single_eq_of_ne hp.symm, show X.Inc (X.M.vtx y) (X.M.edge (X.M.a1 y)) from
    ⟨_, vtx_a1 y, rfl⟩, show X.Inc (X.M.vtx y) (X.M.edge (X.M.a1 (X.M.a2 y))) from
    ⟨_, by simp, rfl⟩] using h0

omit [Fintype D] in
theorem meets_of {l Δ : L} (h : l ≠ Δ) : ∃ e, X.lineE e = l ∧ ∃ w, X.Inc w e ∧ X.On w Δ := by
  obtain ⟨q, ⟨⟨x, hx, hxl⟩, hq⟩, -⟩ := X.meet l Δ h
  exact ⟨X.M.edge x, hxl, q, ⟨x, hx, rfl⟩, hq⟩

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

open Classical in
omit [Fintype D] [Fintype D'] in
theorem SkelIso.mapC_single (f : SkelIso X X') (e : X.M.Edge) :
    f.mapC (Pi.single e 1) = Pi.single (f.fE e) 1 := by
  funext e'
  obtain ⟨e0, rfl⟩ := f.fE.surjective e'
  simp [Pi.single_apply]

open Classical in
/-- **A skeleton isomorphism of simple arrangements carries face paths to face paths.** -/
theorem path_map (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (h2 : ∀ y : D, X.nu (X.M.vtx y) = 2) (h2' : ∀ y : D', X'.nu (X'.M.vtx y) = 2)
    (f : SkelIso X X') {e1 e e2 : X.M.Edge} (h : X.Path3 e1 e e2) :
    X'.Path3 (f.fE e1) (f.fE e) (f.fE e2) := by
  obtain ⟨d, rfl, rfl, rfl⟩ := h
  have ham : X.line (X.M.a1 d) ≠ X.line d := line_a1_ne hs d
  have hbm : X.line (X.M.a1 (X.M.a0 d)) ≠ X.line d := by
    have := line_a1_ne hs (X.M.a0 d); rwa [X.line_a0] at this
  have hvw := noLoop hbf d
  have va : X.On (X.M.vtx d) (X.line (X.M.a1 d)) := ⟨X.M.a1 d, vtx_a1 d, rfl⟩
  have vm : X.On (X.M.vtx d) (X.line d) := ⟨d, rfl, rfl⟩
  have wb : X.On (X.M.vtx (X.M.a0 d)) (X.line (X.M.a1 (X.M.a0 d))) := ⟨_, vtx_a1 _, rfl⟩
  have wm : X.On (X.M.vtx (X.M.a0 d)) (X.line d) := ⟨_, rfl, X.line_a0 d⟩
  have nwa : ¬X.On (X.M.vtx (X.M.a0 d)) (X.line (X.M.a1 d)) := fun h => hvw (meet_eq ham h wm va vm)
  have nvb : ¬X.On (X.M.vtx d) (X.line (X.M.a1 (X.M.a0 d))) := fun h => hvw (meet_eq hbm wb wm h vm)
  have hab : X.line (X.M.a1 d) ≠ X.line (X.M.a1 (X.M.a0 d)) := fun h => nwa (h ▸ wb)
  obtain ⟨p, ⟨pa, pb⟩, -⟩ := X.meet _ _ hab
  have hpv : p ≠ X.M.vtx d := fun h => nvb (h ▸ pb)
  have hpw : p ≠ X.M.vtx (X.M.a0 d) := fun h => nwa (h ▸ pa)
  obtain ⟨Pa, sa, ba, ha⟩ := seg_start hbf hs va pa (e1 := X.M.edge (X.M.a1 d)) rfl
  obtain ⟨Pb, sb, bb, hb⟩ := seg_start hbf hs wb pb (e1 := X.M.edge (X.M.a1 (X.M.a0 d))) rfl
  -- a fourth line avoiding the triangle
  obtain ⟨q1, q2, q3, o1, o2, o3, n12, n13, n23⟩ := hbf (X.line (X.M.a1 d))
  obtain ⟨q, oq, hqv, hqp⟩ : ∃ q, X.On q (X.line (X.M.a1 d)) ∧ q ≠ X.M.vtx d ∧ q ≠ p := by
    by_contra hc
    push Not at hc
    have k := fun q (hq : X.On q (X.line (X.M.a1 d))) => (eq_or_ne q (X.M.vtx d)).imp_right (hc q hq)
    rcases k _ o1 with rfl | rfl <;> rcases k _ o2 with h2 | h2 <;> rcases k _ o3 with h3 | h3 <;>
      simp_all
  obtain ⟨x, rfl, hx⟩ := oq
  obtain ⟨y, hyv, hyl⟩ := X.two x
  set Δ := X.line y
  have hΔa : Δ ≠ X.line (X.M.a1 d) := hx ▸ hyl
  have oΔ : X.On (X.M.vtx x) Δ := ⟨y, hyv, rfl⟩
  have hΔm : X.line d ≠ Δ := fun h => hqv (meet_eq ham ⟨x, rfl, hx⟩ (h ▸ oΔ) va vm)
  have hΔb : X.line (X.M.a1 (X.M.a0 d)) ≠ Δ := fun h => hqp (meet_eq hab ⟨x, rfl, hx⟩ (h ▸ oΔ) pa pb)
  have nv : ¬X.On (X.M.vtx d) Δ := fun h => hΔa (two_lines hs (h2 d) h hΔm.symm)
  have nw : ¬X.On (X.M.vtx (X.M.a0 d)) Δ := fun h => hΔb.symm (two_lines hs (h2 _) h
    (by rw [X.line_a0]; exact hΔm.symm))
  have np : ¬X.On p Δ := by
    obtain ⟨z, rfl, hz⟩ := pa
    intro h
    have e1 := two_lines hs (h2 z) h (hz ▸ hΔa)
    have e2 := two_lines hs (h2 z) pb (hz ▸ hab.symm)
    exact hΔb (e2.trans e1.symm)
  have ss : ∀ ε, (Pi.single (X.M.edge d) 1 : X.M.Edge → ZMod 2) ε ≠ 0 → X.lineE ε = X.line d :=
    fun ε h => by
      by_cases hε : ε = X.M.edge d
      · rw [hε]; rfl
      · exact absurd (Pi.single_eq_of_ne hε _) h
  obtain ⟨_, hem⟩ := meets_of hΔm
  obtain ⟨_, hea⟩ := meets_of hΔa.symm
  obtain ⟨_, heb⟩ := meets_of hΔb
  have hT' := (f.triangle_map hbf hbf' hs hs' ⟨vm, va⟩ ⟨pa, pb⟩ ⟨wb, wm⟩ ham.symm nvb ⟨nv, np, nw⟩
    ss sa sb (bd_single hbf d) ba (by rw [bb, add_comm]) hem hea heb).1
    (path_bounds hbf hs d sa sb ba bb ha hb)
  rw [SkelIso.mapC_single] at hT'
  -- the image in `X'`
  obtain ⟨d0, hd0v, hd0e⟩ := (f.inc _ _).1 (⟨d, rfl, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge d))
  have l0 : X'.line d0 = f.fL (X.line d) := by rw [← lineE_edge, hd0e, f.line]; rfl
  have i1 := (f.inc _ _).1 (⟨_, vtx_a1 d, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge (X.M.a1 d)))
  have la : X'.lineE (f.fE (X.M.edge (X.M.a1 d))) = f.fL (X.line (X.M.a1 d)) := f.line _
  obtain ⟨d', hv', he', h1'⟩ : ∃ d', X'.M.vtx d' = f.fV (X.M.vtx d) ∧
      X'.M.edge d' = f.fE (X.M.edge d) ∧ X'.M.edge (X'.M.a1 d') = f.fE (X.M.edge (X.M.a1 d)) := by
    rcases corner2 hbf' hs' (h2' d0) (hd0v ▸ i1) (by rw [la, l0]; exact f.fL.injective.ne ham)
      with h | h
    exacts [⟨d0, hd0v, hd0e, h.symm⟩, ⟨_, by simp [hd0v], by simp [hd0e], h.symm⟩]
  have l' : X'.line d' = f.fL (X.line d) := by rw [← lineE_edge, he', f.line]; rfl
  have hw' : X'.M.vtx (X'.M.a0 d') = f.fV (X.M.vtx (X.M.a0 d)) := by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
    rw [← he', inc_iff] at this
    exact (this.resolve_left fun h => hvw (f.fV.injective (h.trans hv'))).symm
  have i2 := (f.inc _ _).1 (⟨_, vtx_a1 _, rfl⟩ :
    X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge (X.M.a1 (X.M.a0 d))))
  rcases corner2 hbf' hs' (h2' (X'.M.a0 d')) (hw' ▸ i2)
    (by rw [f.line, X'.line_a0, l']; exact f.fL.injective.ne hbm) with h3 | h3
  · exact ⟨d', h1', he', h3.symm⟩
  exfalso
  -- the other side of `e`: its face path triangle would bound too
  have la2 : X'.line (X'.M.a1 (X'.M.a2 d')) = f.fL (X.line (X.M.a1 d)) := by
    rw [two_lines hs' (h2' d') ⟨X'.M.a1 (X'.M.a2 d'), by simp, rfl⟩
      (by have := line_a1_ne hs' (X'.M.a2 d'); rwa [X'.line_a2] at this), ← lineE_edge, h1', f.line]
    rfl
  obtain ⟨Q, sQ, bQ, hQ⟩ := seg_start hbf' hs' (f.on_map.1 va) (f.on_map.1 pa)
    (e1 := X'.M.edge (X'.M.a1 (X'.M.a2 d'))) la2
  have r : X'.M.a0 (X'.M.a2 d') = X'.M.a2 (X'.M.a0 d') := X'.M.a0_a2 d'
  have hT2 := path_bounds hbf' hs' (X'.M.a2 d') (p := f.fV p) (Pa := Q) (Pb := f.mapC Pb)
    (by rwa [la2]) (by rw [r, ← lineE_edge, ← h3, f.line]; exact f.supp_map sb)
    (by simpa [hv'] using bQ) (by simpa [r, hw'] using f.bd_map bb) hQ
    (by rw [r, ← h3, SkelIso.mapC_apply, hb])
  rw [edge_a2, he'] at hT2
  rcases seg_unique hbf' hs' (f.supp_map sa) sQ (by rw [f.bd_map ba, bQ]) with hq | hq
  · have := seg_end2 hbf' hs' (h2' d') (P := f.mapC Pa) (p := f.fV p)
      (by rw [← lineE_edge, h1', f.line]; exact f.supp_map sa) (by rw [f.bd_map ba, hv'])
      (fun h => hpv (f.fV.injective (h.trans hv')))
    rw [h1', SkelIso.mapC_apply, ha, ← hq, hQ] at this
    exact absurd this (by decide)
  · refine lineChain_not_mem hbf' hs' (f.fL.injective.ne ham) ?_
    convert X'.B1.add_mem hT' hT2 using 1
    rw [hq]
    exact funext fun _ => (by decide : ∀ s x y c : ZMod 2, c = s + x + y + (s + (x + c) + y)) _ _ _ _

/-- **Full faithfulness for simple arrangements** (page 54, when every vertex is on exactly two
lines). Every isomorphism of decomposed skeleta of two simple bigon-free arrangements that go
straight comes from a unique isomorphism of the arrangements. -/
theorem full_simple (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (h2 : ∀ y : D, X.nu (X.M.vtx y) = 2)
    (h2' : ∀ y : D', X'.nu (X'.M.vtx y) = 2) (f : SkelIso X X') :
    ∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d) :=
  (lift_iff hbf hbf' hs hs' f).2 fun _ _ _ => ⟨path_map hbf hbf' hs hs' h2 h2' f, fun h => by
    simpa [SkelIso.symm] using path_map hbf' hbf hs' hs h2' h2 f.symm h⟩

end Simple

/-! ### Sides of an edge: the transport (A4) of page 50 -/

section Sides

open Matrix

/-- Half a turn after `y` meets each other line once: a chain on the line of the `(j+1)`-th
edge-end after `y` (before the opposite end of `y`), with value `1` there, has sum `1` on the
half turn. -/
theorem half_one_gen (hs : X.Straight) (y : D) {j : ℕ} (hj : j + 1 < X.nu (X.M.vtx y)) {l : L}
    {P : X.M.Edge → ZMod 2} (hP : ∀ e, P e ≠ 0 → X.lineE e = l)
    (hl : X.line ((X.phi ^ (j + 1)) y) = l) (h1 : P (X.M.edge ((X.phi ^ (j + 1)) y)) = 1) :
    ∑ i ∈ Finset.range (X.nu (X.M.vtx y)), P (X.M.edge ((X.phi ^ (i + 1)) y)) = 1 := by
  have sh : ∀ i, (X.phi ^ (i + 1)) y = (X.phi ^ i) (X.phi y) := fun i => by
    rw [pow_succ, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single j]
  · exact h1
  · intro i hi hij
    have hi := Finset.mem_range.1 hi
    refine by_contra fun h => ?_
    have e : X.line ((X.phi ^ i) (X.phi y)) = X.line ((X.phi ^ j) (X.phi y)) := by
      rw [← sh, ← sh, hl, ← hP _ h, lineE_edge]
    rcases Nat.lt_or_gt_of_ne hij with h' | h'
    · exact line_inj hs (X.phi y) h' (by simp; omega) e
    · exact line_inj hs (X.phi y) h' (by simp; omega) e.symm
  · exact fun h => absurd (Finset.mem_range.2 (by omega)) h

open Classical in
/-- **Triangles leaving an edge on one side bound** (the general form of `path_bounds`). Let
`e = edge d` join `v` to `w`, `e1` the `(j+1)`-th and `e2` the `(k+1)`-th edge-end after `d`
at `v` and after `a0 d` at `w`, both strictly within the half turn on the side of the face of
`d`, and `Pa`, `Pb` segments of their lines from `v`, `w` to a common vertex starting with
them. Then the triangle `e + Pa + Pb` bounds. -/
theorem side_bounds (hbf : BigonFree X.On) (hs : X.Straight) (d : D) {j k : ℕ}
    (hj : j + 1 < X.nu (X.M.vtx d)) (hk : k + 1 < X.nu (X.M.vtx (X.M.a0 d))) {p : X.M.Vtx}
    {Pa Pb : X.M.Edge → ZMod 2} (sa : ∀ e, Pa e ≠ 0 → X.lineE e = X.line ((X.phi ^ (j + 1)) d))
    (sb : ∀ e, Pb e ≠ 0 → X.lineE e = X.line ((X.phi ^ (k + 1)) (X.M.a0 d)))
    (ba : X.incM *ᵥ Pa = Pi.single (X.M.vtx d) 1 + Pi.single p 1)
    (bb : X.incM *ᵥ Pb = Pi.single (X.M.vtx (X.M.a0 d)) 1 + Pi.single p 1)
    (ha : Pa (X.M.edge ((X.phi ^ (j + 1)) d)) = 1)
    (hb : Pb (X.M.edge ((X.phi ^ (k + 1)) (X.M.a0 d))) = 1) :
    Pi.single (X.M.edge d) 1 + Pa + Pb ∈ X.B1 := by
  set a := X.line ((X.phi ^ (j + 1)) d)
  set b := X.line ((X.phi ^ (k + 1)) (X.M.a0 d))
  have ham : a ≠ X.line d := fun h => line_inj hs d (Nat.succ_pos j) hj (by simpa using h.symm)
  have hbm : b ≠ X.line d := fun h => line_inj hs (X.M.a0 d) (Nat.succ_pos k) hk
    (by rw [pow_zero, Equiv.Perm.one_apply, X.line_a0]; exact h.symm)
  have hvw := noLoop hbf d
  have va : X.On (X.M.vtx d) a := ⟨_, vtx_phi' _ _, rfl⟩
  have vm : X.On (X.M.vtx d) (X.line d) := ⟨d, rfl, rfl⟩
  have wb : X.On (X.M.vtx (X.M.a0 d)) b := ⟨_, vtx_phi' _ _, rfl⟩
  have wm : X.On (X.M.vtx (X.M.a0 d)) (X.line d) := ⟨_, rfl, X.line_a0 d⟩
  have nwa : ¬X.On (X.M.vtx (X.M.a0 d)) a := fun h => hvw (meet_eq ham h wm va vm)
  have nvb : ¬X.On (X.M.vtx d) b := fun h => hvw (meet_eq hbm wb wm h vm)
  have sc : ∀ e, X.lineChain a e ≠ 0 → X.lineE e = a := fun e h => by_contra fun h' => h (by
    simp [lineChain, h'])
  have p0 : ∀ {P : X.M.Edge → ZMod 2} {l}, (∀ e, P e ≠ 0 → X.lineE e = l) → ∀ {ε},
      X.lineE ε ≠ l → P ε = 0 := fun hP ε h => by_contra fun h' => h (hP ε h')
  have hz : Pi.single (X.M.edge d) 1 + Pa + Pb ∈ X.Z1 := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_add, bd_single hbf d, ba,
      bb]
    exact funext fun v => (by decide : ∀ x y q : ZMod 2, x + y + (x + q) + (y + q) = 0) _ _ _
  rw [flip hbf hs ham hz]
  rintro ⟨S, hS⟩
  simp only [Matrix.mulVecLin_apply] at hS
  have key := edge_parity hbf hs S d (fun ε hε hne => by
      rw [hS, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hne,
        p0 sa fun h => ham (h.symm.trans hε), p0 sb fun h => hbm (h.symm.trans hε),
        p0 sc fun h => ham (h.symm.trans hε)]
      simp)
    fun q hq hqv hqw ε hε => by
      have hqa : ¬X.On q a := fun h => hqv (meet_eq ham h hq va vm)
      have hqb : ¬X.On q b := fun h => hqw (meet_eq hbm h hq wb wm)
      rw [hS, Pi.add_apply, Pi.add_apply, Pi.add_apply, off_line sa hqa hε, off_line sb hqb hε,
        off_line sc hqa hε, Pi.single_eq_of_ne fun h => by
          rcases (inc_iff d q).1 (h ▸ hε) with h' | h'
          exacts [hqv h', hqw h']]
      simp
  rw [hS] at key
  simp only [Pi.add_apply, Finset.sum_add_distrib] at key
  have e2 := half_edge hbf (X.M.a0 d)
  rw [edge_a0] at e2
  rw [half_edge hbf d, e2, half_one_gen hs d hj sa rfl ha, half_zero d sb nvb,
    half_one_gen hs d hj sc rfl (by simp [lineChain, a]), half_zero _ sa nwa,
    half_one_gen hs (X.M.a0 d) hk sb rfl hb, half_zero _ sc nwa] at key
  exact absurd key (by decide)

open Classical in
/-- `φ` has period `2ν` at every flag: the `2ν` edge-ends at a vertex are a cycle. -/
theorem phi_period (x : D) : (X.phi ^ (2 * X.nu (X.M.vtx x))) x = x := by
  set ν := X.nu (X.M.vtx x)
  let g : ℕ × Bool → D := fun q => if q.2 then X.M.a2 ((X.phi ^ q.1) x) else (X.phi ^ q.1) x
  have pinj : ∀ {i i' : ℕ}, i < 2 * ν → i' < 2 * ν → (X.phi ^ i) x = (X.phi ^ i') x → i = i' := by
      intro i i' hi hi' h
      rcases lt_trichotomy i i' with h' | h' | h'
      exacts [(pow_ne x h' hi' h).elim, h', (pow_ne x h' hi h.symm).elim]
  have hA : (((Finset.range (2 * ν)) ×ˢ (Finset.univ : Finset Bool)).image g).card = 4 * ν := by
    rw [Finset.card_image_of_injOn]
    · simp; ring
    rintro ⟨i, b⟩ hi ⟨i', b'⟩ hi' h
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hi hi'
    cases b <;> cases b' <;> simp only [g, Bool.false_eq_true, ite_false, ite_true] at h
    · rw [pinj hi.1 hi'.1 h]
    · exact (a2_ne_pow i' i x h.symm).elim
    · exact (a2_ne_pow i i' x h).elim
    · rw [pinj hi.1 hi'.1 (by simpa [X.M.a2_a2] using congrArg X.M.a2 h)]
  have heq := Finset.eq_of_subset_of_card_le (s := ((Finset.range (2 * ν)) ×ˢ
    (Finset.univ : Finset Bool)).image g) (t := Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x)
    (fun y hy => by
      obtain ⟨⟨i, b⟩, -, rfl⟩ := Finset.mem_image.1 hy
      cases b <;> simp [g])
    (by rw [card_vtx, hA])
  obtain ⟨⟨i, b⟩, hi, h⟩ := Finset.mem_image.1 (heq ▸ (by simp :
    (X.phi ^ (2 * ν)) x ∈ Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x))
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at hi
  cases b
  · simp only [g, Bool.false_eq_true, ite_false] at h
    have := four_nu_le ((X.phi ^ i) x) (q := 2 * ν - i) (by omega) (by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hi.le, ← h])
    rw [vtx_phi'] at this
    obtain rfl : i = 0 := by omega
    simpa using h.symm
  · exact (a2_ne_pow i _ x h).elim

open Classical in
/-- At the end `vtx x` of a segment of the line of `x`, the segment is `1` on exactly one of the
two edges of that line. -/
theorem seg_end (hbf : BigonFree X.On) (hs : X.Straight) (x : D) {P : X.M.Edge → ZMod 2}
    {p : X.M.Vtx} (hP : ∀ e, P e ≠ 0 → X.lineE e = X.line x)
    (hb : X.incM *ᵥ P = Pi.single (X.M.vtx x) 1 + Pi.single p 1) (hp : p ≠ X.M.vtx x) :
    P (X.M.edge x) + P (X.M.edge ((X.phi ^ X.nu (X.M.vtx x)) x)) = 1 := by
  have h0 := congrFun hb (X.M.vtx x)
  rw [incM_mulVec, Finset.sum_congr rfl
    (g := fun e => if X.Inc (X.M.vtx x) e ∧ X.lineE e = X.line x then P e else 0) fun e _ => by
      by_cases h1 : X.Inc (X.M.vtx x) e <;> by_cases h2 : X.lineE e = X.line x <;> simp [h1, h2]
      exact by_contra fun h => h2 (hP e h), ← Finset.sum_filter, (line_edges hbf hs x).1,
    Finset.sum_pair (line_edges hbf hs x).2] at h0
  simpa [Pi.single_eq_of_ne hp.symm] using h0

open Classical in
/-- **Triangles leaving an edge on opposite sides do not bound.** With the notation of
`side_bounds`, but `e2` taken on the side of the face of `a2 d` (after `a0 (a2 d)` at `w`), the
triangle `e + Pa + Pb` does not bound. With `side_bounds`: whether two edges at the two ends of
`e` leave it on the same side is read on the bounding triangles, that is (A4). -/
theorem side_not (hbf : BigonFree X.On) (hs : X.Straight) (d : D) {j k : ℕ}
    (hj : j + 1 < X.nu (X.M.vtx d)) (hk : k + 1 < X.nu (X.M.vtx (X.M.a0 d))) {p : X.M.Vtx}
    (hpv : p ≠ X.M.vtx d) {Pa Pb : X.M.Edge → ZMod 2}
    (sa : ∀ e, Pa e ≠ 0 → X.lineE e = X.line ((X.phi ^ (j + 1)) d))
    (sb : ∀ e, Pb e ≠ 0 → X.lineE e = X.line ((X.phi ^ (k + 1)) (X.M.a0 (X.M.a2 d))))
    (ba : X.incM *ᵥ Pa = Pi.single (X.M.vtx d) 1 + Pi.single p 1)
    (bb : X.incM *ᵥ Pb = Pi.single (X.M.vtx (X.M.a0 d)) 1 + Pi.single p 1)
    (ha : Pa (X.M.edge ((X.phi ^ (j + 1)) d)) = 1)
    (hb : Pb (X.M.edge ((X.phi ^ (k + 1)) (X.M.a0 (X.M.a2 d)))) = 1) :
    Pi.single (X.M.edge d) 1 + Pa + Pb ∉ X.B1 := by
  intro hT
  set ν := X.nu (X.M.vtx d)
  set a := X.line ((X.phi ^ (j + 1)) d)
  have ham : a ≠ X.line d := fun h => line_inj hs d (Nat.succ_pos j) hj (by simpa using h.symm)
  -- the other edge of `a` at `v`, seen from `a2 d`
  have key : (X.phi ^ (ν - (j + 1))) (X.M.a2 d) = X.M.a2 ((X.phi ^ (ν + (j + 1))) d) := by
    have hp := phi_period (X := X) (X.M.a2 d)
    rw [vtx_a2] at hp
    rw [show (X.phi ^ (ν + (j + 1))) d = (X.phi ^ ((ν + (j + 1) : ℕ) : ℤ)) d by
      rw [zpow_natCast], a2_zpow]
    conv_rhs => rw [← hp]
    rw [← Equiv.Perm.mul_apply, ← zpow_natCast X.phi (2 * ν), ← _root_.zpow_add,
      ← zpow_natCast X.phi (ν - (j + 1))]
    congr 2; omega
  have hν : X.nu (X.M.vtx ((X.phi ^ (j + 1)) d)) = ν := by rw [vtx_phi']
  have hx : (X.phi ^ ν) ((X.phi ^ (j + 1)) d) = (X.phi ^ (ν + (j + 1))) d := by
    rw [← Equiv.Perm.mul_apply, ← pow_add]
  have e0 := seg_end hbf hs ((X.phi ^ (j + 1)) d) sa (by rw [vtx_phi']; exact ba)
    (by rw [vtx_phi']; exact hpv)
  rw [ha, hν, hx] at e0
  have z0 : Pa (X.M.edge ((X.phi ^ (ν + (j + 1))) d)) = 0 := by
    linear_combination e0
  have hj' : ν - (j + 1) - 1 + 1 = ν - (j + 1) := by omega
  have la2 : X.line ((X.phi ^ (ν + (j + 1))) d) = a := by rw [← hx, ← hν]; exact hs _
  have la : X.line ((X.phi ^ (ν - (j + 1) - 1 + 1)) (X.M.a2 d)) = a := by
    rw [hj', key, X.line_a2, la2]
  have hT2 := side_bounds hbf hs (X.M.a2 d) (j := ν - (j + 1) - 1) (k := k) (p := p)
    (Pa := Pa + X.lineChain a) (Pb := Pb) (by rw [vtx_a2]; omega)
    (by rw [X.M.a0_a2, vtx_a2]; exact hk)
    (fun e h => by
      rw [la]
      by_contra h'
      exact h (by simp [lineChain, h', by_contra fun h'' => h' (sa e h'')]))
    sb (by rw [Matrix.mulVec_add, ba, show X.incM *ᵥ X.lineChain a = 0 from
      lineChain_mem hbf hs a, add_zero, vtx_a2])
    (by rw [X.M.a0_a2, vtx_a2]; exact bb)
    (by rw [Pi.add_apply, hj', key, edge_a2, z0]; simp [lineChain, la2]) hb
  rw [edge_a2] at hT2
  refine lineChain_not_mem hbf hs ham ?_
  convert X.B1.add_mem hT hT2 using 1
  exact funext fun _ => (by decide : ∀ s x y c : ZMod 2, c = s + x + y + (s + (x + c) + y)) _ _ _ _

end Sides

/-! ### The cyclic order at a vertex: (A1)–(A3) -/

section Order

variable (X) in
/-- The edge `ε` leaves the vertex of `x` strictly on the side of the flag `x` of its edge:
it is the end of one of the `ν - 1` edge-ends after `x` and before the opposite end. -/
def Side (x : D) (ε : X.M.Edge) : Prop :=
  ∃ j, j + 1 < X.nu (X.M.vtx x) ∧ X.M.edge ((X.phi ^ (j + 1)) x) = ε

/-- Edge-ends at a vertex are distinct along a full turn. -/
theorem edge_pow_inj (hbf : BigonFree X.On) (x : D) {i j : ℕ} (hi : i < 2 * X.nu (X.M.vtx x))
    (hj : j < 2 * X.nu (X.M.vtx x)) (h : X.M.edge ((X.phi ^ i) x) = X.M.edge ((X.phi ^ j) x)) :
    i = j := by
  rcases (at_edge hbf).1 ⟨by simp, h⟩ with h' | h'
  · rcases lt_trichotomy i j with c | c | c
    exacts [(pow_ne x c hj h').elim, c, (pow_ne x c hi h'.symm).elim]
  · exact (a2_ne_pow j i x h'.symm).elim

/-- `φ^i a2 = a2 φ^(2ν - i)`. -/
theorem pow_a2 (x : D) {i : ℕ} (hi : i ≤ 2 * X.nu (X.M.vtx x)) :
    (X.phi ^ i) (X.M.a2 x) = X.M.a2 ((X.phi ^ (2 * X.nu (X.M.vtx x) - i)) x) := by
  have hp := phi_period (X := X) (X.M.a2 x)
  rw [vtx_a2] at hp
  rw [show (X.phi ^ (2 * X.nu (X.M.vtx x) - i)) x =
      (X.phi ^ ((2 * X.nu (X.M.vtx x) - i : ℕ) : ℤ)) x by rw [zpow_natCast], a2_zpow]
  conv_rhs => rw [← hp]
  rw [← Equiv.Perm.mul_apply, ← zpow_natCast X.phi (2 * X.nu (X.M.vtx x)), ← _root_.zpow_add,
    ← zpow_natCast X.phi i]
  congr 2; omega

/-- The two sides of an edge at a vertex are disjoint. -/
theorem side_disj (hbf : BigonFree X.On) {x : D} {ε : X.M.Edge} (h1 : X.Side x ε)
    (h2 : X.Side (X.M.a2 x) ε) : False := by
  obtain ⟨i, hi, rfl⟩ := h1
  obtain ⟨j, hj, h⟩ := h2
  rw [vtx_a2] at hj
  rw [pow_a2 x (by omega), edge_a2] at h
  have := edge_pow_inj hbf x (by omega) (by omega) h
  omega

/-- Every edge at a vertex off the line of `x` leaves on one of the two sides of the edge of
`x`. -/
theorem side_cover (hs : X.Straight) (x : D) {ε : X.M.Edge}
    (hε : X.Inc (X.M.vtx x) ε) (hl : X.lineE ε ≠ X.line x) : X.Side x ε ∨ X.Side (X.M.a2 x) ε := by
  classical
  obtain ⟨z, hz, rfl⟩ := hε
  obtain ⟨k, hk⟩ := vtx_orbit hz
  have hν : 0 < X.nu (X.M.vtx x) :=
    Finset.card_pos.2 ⟨X.line x, Finset.mem_image.2 ⟨x, by simp, rfl⟩⟩
  have hr : (X.phi ^ k) x = (X.phi ^ (k % (2 * X.nu (X.M.vtx x) : ℕ)).toNat) x := by
    have h' : ((X.phi ^ ((2 * X.nu (X.M.vtx x) : ℕ) : ℤ)) ^ (k / (2 * X.nu (X.M.vtx x) : ℕ))) x =
        x := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by rw [zpow_natCast]; exact phi_period x) _
    conv_lhs => rw [← Int.emod_add_mul_ediv k (2 * X.nu (X.M.vtx x) : ℕ), zpow_add,
      Equiv.Perm.mul_apply, zpow_mul, h']
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  have hlt : (k % (2 * X.nu (X.M.vtx x) : ℕ)).toNat < 2 * X.nu (X.M.vtx x) := by
    have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < (2 * X.nu (X.M.vtx x) : ℕ)); omega
  generalize (k % (2 * X.nu (X.M.vtx x) : ℕ)).toNat = i at hr hlt
  have he : X.M.edge z = X.M.edge ((X.phi ^ i) x) := by rcases hk with rfl | rfl <;> simp [hr]
  by_cases h0 : i = 0
  · exact (hl (by simp [he, h0])).elim
  by_cases hν' : i = X.nu (X.M.vtx x)
  · exact (hl (by rw [he, hν', lineE_edge]; exact hs x)).elim
  rcases Nat.lt_or_gt_of_ne hν' with h1 | h1
  · exact .inl ⟨i - 1, by omega, by rw [Nat.sub_add_cancel (by omega)]; exact he.symm⟩
  · refine .inr ⟨2 * X.nu (X.M.vtx x) - i - 1, by rw [vtx_a2]; omega, ?_⟩
    rw [show 2 * X.nu (X.M.vtx x) - i - 1 + 1 = 2 * X.nu (X.M.vtx x) - i by omega,
      pow_a2 x (by omega), edge_a2, show 2 * X.nu (X.M.vtx x) - (2 * X.nu (X.M.vtx x) - i) = i by
        omega, he]

/-- **Adjacency from betweenness.** The `i`-th edge-end after `x` (`1 ≤ i < ν`) is the next one,
`i = 1`, iff no edge lies on its side of the edge of `x` and, at the same time, on the side
of the edge of `x` with respect to it. -/
theorem between_iff (hbf : BigonFree X.On) (x : D) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i < X.nu (X.M.vtx x)) :
    (∃ ζ, X.Side x ζ ∧ X.Side (X.M.a2 ((X.phi ^ i) x)) ζ) ↔ 1 < i := by
  have hp := phi_period (X := X) x
  constructor
  · rintro ⟨ζ, ⟨k, hk, rfl⟩, ⟨l, hl, h⟩⟩
    simp only [vtx_a2, vtx_phi'] at hl
    rw [pow_a2 _ (by simp only [vtx_phi']; omega), edge_a2, vtx_phi', ← Equiv.Perm.mul_apply,
      ← pow_add] at h
    rcases Nat.lt_or_ge i (l + 1) with c | c
    · have := edge_pow_inj hbf x (by omega) (by omega) h
      omega
    · rw [show 2 * X.nu (X.M.vtx x) - (l + 1) + i = i - (l + 1) + 2 * X.nu (X.M.vtx x) by omega,
        pow_add, Equiv.Perm.mul_apply, hp] at h
      have := edge_pow_inj hbf x (by omega) (by omega) h
      omega
  · intro h1
    refine ⟨_, ⟨0, by omega, rfl⟩, ⟨i - 2, by simp only [vtx_a2, vtx_phi']; omega, ?_⟩⟩
    rw [pow_a2 _ (by simp only [vtx_phi']; omega), edge_a2, vtx_phi', ← Equiv.Perm.mul_apply,
      ← pow_add, show 2 * X.nu (X.M.vtx x) - (i - 2 + 1) + i = 0 + 1 + 2 * X.nu (X.M.vtx x) by
        omega, pow_add, Equiv.Perm.mul_apply, hp]

end Order

/-! ### Corners are read on the skeleton when every triangle has a fourth line -/

section Corners

open Matrix

theorem one_lt_nu (y : D) : 1 < X.nu (X.M.vtx y) := by
  classical
  obtain ⟨e, he, hl⟩ := X.two y
  exact Finset.one_lt_card.2 ⟨_, Finset.mem_image.2 ⟨y, by simp, rfl⟩, _,
    Finset.mem_image.2 ⟨e, by simp [he], rfl⟩, Ne.symm hl⟩

theorem side_line (hs : X.Straight) {x : D} {ε : X.M.Edge} (h : X.Side x ε) :
    X.Inc (X.M.vtx x) ε ∧ X.lineE ε ≠ X.line x := by
  obtain ⟨j, hj, rfl⟩ := h
  exact ⟨⟨_, vtx_phi' _ _, rfl⟩, fun h => line_inj hs x (Nat.succ_pos j) hj (by simpa using h.symm)⟩

/-- The edge after `x` leaves on the side of `x`. -/
theorem side_one (x : D) : X.Side x (X.M.edge (X.M.a1 x)) :=
  ⟨0, one_lt_nu x, by simp [phi_apply]⟩

/-- Seen from the `i`-th edge-end after `x`, the edge of `x` is on the side of `a2`. -/
theorem side_back (x : D) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < X.nu (X.M.vtx x)) :
    X.Side (X.M.a2 ((X.phi ^ i) x)) (X.M.edge x) := by
  refine ⟨i - 1, by simp only [vtx_a2, vtx_phi']; omega, ?_⟩
  rw [Nat.sub_add_cancel hi1, pow_a2 _ (by simp only [vtx_phi']; omega), edge_a2, vtx_phi',
    ← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega), phi_period]

open Classical in
variable (X) in
/-- The triangle cut out by `e` (from `v` to `w`) and the edges `ζ` at `v` and `η` at `w`
bounds: segments of their lines starting with them meet at `p`, and with `e` they bound. -/
def Tri (v w : X.M.Vtx) (e ζ η : X.M.Edge) : Prop :=
  ∃ (p : X.M.Vtx) (P Q : X.M.Edge → ZMod 2), (∀ e', P e' ≠ 0 → X.lineE e' = X.lineE ζ) ∧
    (∀ e', Q e' ≠ 0 → X.lineE e' = X.lineE η) ∧ X.incM *ᵥ P = Pi.single v 1 + Pi.single p 1 ∧
    X.incM *ᵥ Q = Pi.single w 1 + Pi.single p 1 ∧ P ζ = 1 ∧ Q η = 1 ∧
    X.On p (X.lineE ζ) ∧ X.On p (X.lineE η) ∧ Pi.single e 1 + P + Q ∈ X.B1

/-- **(A4) as an equivalence.** For `η` leaving the far end of the edge of `x` on the side of
`a0 x`, an edge `ζ` at the vertex of `x` leaves on the side of `x` iff their triangle bounds. -/
theorem side_tri (hbf : BigonFree X.On) (hs : X.Straight) (x : D) {ζ η : X.M.Edge}
    (hζ : X.Side x ζ ∨ X.Side (X.M.a2 x) ζ) (hη : X.Side (X.M.a0 x) η) :
    X.Tri (X.M.vtx x) (X.M.vtx (X.M.a0 x)) (X.M.edge x) ζ η ↔ X.Side x ζ := by
  have hvw := noLoop hbf x
  obtain ⟨hηi, hηl⟩ := side_line hs hη
  rw [X.line_a0] at hηl
  have wη : X.On (X.M.vtx (X.M.a0 x)) (X.lineE η) := on_of_inc hηi
  have wm : X.On (X.M.vtx (X.M.a0 x)) (X.line x) := ⟨_, rfl, X.line_a0 x⟩
  have vm : X.On (X.M.vtx x) (X.line x) := ⟨x, rfl, rfl⟩
  have nvη : ¬X.On (X.M.vtx x) (X.lineE η) := fun h => hvw (meet_eq hηl wη wm h vm)
  obtain ⟨k, hk, rfl⟩ := hη
  constructor
  · rintro ⟨p, P, Q, sP, sQ, bP, bQ, hP, hQ, -, pη, hT⟩
    refine hζ.resolve_right fun ⟨j, hj, hjz⟩ => ?_
    subst hjz
    refine side_not hbf hs (X.M.a2 x) (p := p) hj (by rw [X.M.a0_a2, vtx_a2]; exact hk)
      (fun h => nvη (by rw [h, vtx_a2] at pη; exact pη)) sP (by simpa [X.M.a2_a2] using sQ)
      (by rw [vtx_a2]; exact bP) (by rw [X.M.a0_a2, vtx_a2]; exact bQ) hP
      (by simpa [X.M.a2_a2] using hQ) ?_
    rwa [edge_a2]
  · rintro ⟨j, hj, rfl⟩
    have vζ : X.On (X.M.vtx x) (X.line ((X.phi ^ (j + 1)) x)) := ⟨_, vtx_phi' _ _, rfl⟩
    have hab : X.line ((X.phi ^ (j + 1)) x) ≠ X.line ((X.phi ^ (k + 1)) (X.M.a0 x)) := fun h =>
      nvη (by rw [lineE_edge, ← h]; exact vζ)
    obtain ⟨p, ⟨pa, pb⟩, -⟩ := X.meet _ _ hab
    obtain ⟨P, sP, bP, hP⟩ := seg_start hbf hs vζ pa (e1 := X.M.edge ((X.phi ^ (j + 1)) x)) rfl
    obtain ⟨Q, sQ, bQ, hQ⟩ := seg_start hbf hs wη pb
      (e1 := X.M.edge ((X.phi ^ (k + 1)) (X.M.a0 x))) rfl
    exact ⟨p, P, Q, sP, sQ, bP, bQ, hP, hQ, pa, pb, side_bounds hbf hs x hj hk sP sQ bP bQ hP hQ⟩

variable (X) in
/-- Every triangle has a fourth line through none of its vertices: no `III₆`-type
obstruction. -/
def FourthLine : Prop := ∀ (a b c : L) (u v w : X.M.Vtx), X.On u a → X.On u b → X.On v b →
  X.On v c → X.On w c → X.On w a → ¬X.On u c → ∃ Δ, ¬X.On u Δ ∧ ¬X.On v Δ ∧ ¬X.On w Δ

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

open Classical in
/-- Skeleton isomorphisms preserve bounding triangles `Tri` when fourth lines exist. -/
theorem SkelIso.tri_map (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (hF : X.FourthLine) (f : SkelIso X X') {v w : X.M.Vtx}
    {e ζ η : X.M.Edge} (hv : X.Inc v e) (hw : X.Inc w e) (hvw : v ≠ w) (hζ : X.Inc v ζ)
    (hη : X.Inc w η) (hζl : X.lineE ζ ≠ X.lineE e) (hηl : X.lineE η ≠ X.lineE e)
    (h : X.Tri v w e ζ η) : X'.Tri (f.fV v) (f.fV w) (f.fE e) (f.fE ζ) (f.fE η) := by
  obtain ⟨p, P, Q, sP, sQ, bP, bQ, hP, hQ, pa, pb, hT⟩ := h
  have vm := on_of_inc hv
  have wm := on_of_inc hw
  have va := on_of_inc hζ
  have wb := on_of_inc hη
  have nvb : ¬X.On v (X.lineE η) := fun h => hvw (meet_eq hηl h vm wb wm)
  obtain ⟨Δ, n1, n2, n3⟩ := hF _ _ _ v p w vm va pa pb wb wm nvb
  have ss : ∀ ε, (Pi.single e 1 : X.M.Edge → ZMod 2) ε ≠ 0 → X.lineE ε = X.lineE e :=
    fun ε h => by
      by_cases hε : ε = e
      · rw [hε]
      · exact absurd (Pi.single_eq_of_ne hε _) h
  have be : X.incM *ᵥ (Pi.single e 1 : X.M.Edge → ZMod 2) = Pi.single v 1 + Pi.single w 1 := by
    obtain ⟨d, rfl, rfl⟩ := hv
    rcases (inc_iff d w).1 hw with h | h
    · exact (hvw h.symm).elim
    · rw [bd_single hbf d, h]
  obtain ⟨_, hem⟩ := meets_of (fun h => n1 (h ▸ vm) : X.lineE e ≠ Δ)
  obtain ⟨_, hea⟩ := meets_of (fun h => n1 (h ▸ va) : X.lineE ζ ≠ Δ)
  obtain ⟨_, heb⟩ := meets_of (fun h => n3 (h ▸ wb) : X.lineE η ≠ Δ)
  have hT' := (f.triangle_map hbf hbf' hs hs' ⟨vm, va⟩ ⟨pa, pb⟩ ⟨wb, wm⟩ hζl.symm nvb ⟨n1, n2, n3⟩
    ss sP sQ be bP (by rw [bQ, add_comm]) hem hea heb).1 hT
  rw [SkelIso.mapC_single] at hT'
  refine ⟨f.fV p, f.mapC P, f.mapC Q, ?_, ?_, f.bd_map bP, f.bd_map bQ, by simpa using hP,
    by simpa using hQ, ?_, ?_, hT'⟩
  · rw [f.line]; exact f.supp_map sP
  · rw [f.line]; exact f.supp_map sQ
  · rw [f.line]; exact f.on_map.1 pa
  · rw [f.line]; exact f.on_map.1 pb

open Classical in
/-- **Sides are read on the skeleton.** If a skeleton isomorphism carries one edge `α` on the
side of `x` to the side of `x'`, it carries every edge on the side of `x` to the side of
`x'`. -/
theorem SkelIso.side_map (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (hF : X.FourthLine) (hF' : X'.FourthLine) (f : SkelIso X X') {x : D}
    {x' : D'} (hv : X'.M.vtx x' = f.fV (X.M.vtx x)) (he : X'.M.edge x' = f.fE (X.M.edge x))
    {α : X.M.Edge} (hα : X.Side x α) (hα' : X'.Side x' (f.fE α)) {ζ : X.M.Edge}
    (hζ' : X'.Inc (X'.M.vtx x') (f.fE ζ)) (hζl' : X'.lineE (f.fE ζ) ≠ X'.line x') :
    X.Side x ζ ↔ X'.Side x' (f.fE ζ) := by
  have hvw := noLoop hbf x
  have hw' : X'.M.vtx (X'.M.a0 x') = f.fV (X.M.vtx (X.M.a0 x)) := by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 x⟩ : X.Inc (X.M.vtx (X.M.a0 x)) (X.M.edge x))
    rw [← he, inc_iff] at this
    exact (this.resolve_left fun h => hvw (f.fV.injective (h.trans hv))).symm
  have l' : X'.line x' = f.fL (X.line x) := by rw [← lineE_edge, he, f.line]; rfl
  have hη := side_one (X := X) (X.M.a0 x)
  obtain ⟨hηi, hηl⟩ := side_line hs hη
  rw [X.line_a0] at hηl
  have fwd : ∀ {ε}, X.Inc (X.M.vtx x) ε → X.lineE ε ≠ X.line x →
      (X.Tri (X.M.vtx x) (X.M.vtx (X.M.a0 x)) (X.M.edge x) ε (X.M.edge (X.M.a1 (X.M.a0 x))) ↔
        X'.Tri (X'.M.vtx x') (X'.M.vtx (X'.M.a0 x')) (X'.M.edge x') (f.fE ε)
          (f.fE (X.M.edge (X.M.a1 (X.M.a0 x))))) := fun hε hεl => by
    rw [hv, hw', he]
    refine ⟨f.tri_map hbf hbf' hs hs' hF ⟨x, rfl, rfl⟩ ⟨_, rfl, edge_a0 x⟩ hvw.symm hε hηi hεl
      hηl, fun h => ?_⟩
    simpa [SkelIso.symm] using f.symm.tri_map hbf' hbf hs' hs hF' ((f.inc _ _).1 ⟨x, rfl, rfl⟩)
      ((f.inc _ _).1 ⟨_, rfl, edge_a0 x⟩) (f.fV.injective.ne hvw.symm) ((f.inc _ _).1 hε)
      ((f.inc _ _).1 hηi) (by rw [f.line, f.line]; exact f.fL.injective.ne hεl)
      (by rw [f.line, f.line]; exact f.fL.injective.ne hηl) h
  have hα0 := side_line hs hα
  have hη' : X'.Side (X'.M.a0 x') (f.fE (X.M.edge (X.M.a1 (X.M.a0 x)))) := by
    have hi : X'.Inc (X'.M.vtx (X'.M.a0 x')) (f.fE (X.M.edge (X.M.a1 (X.M.a0 x)))) := by
      rw [hw']; exact (f.inc _ _).1 hηi
    have hl : X'.lineE (f.fE (X.M.edge (X.M.a1 (X.M.a0 x)))) ≠ X'.line (X'.M.a0 x') := by
      rw [f.line, X'.line_a0, l']; exact f.fL.injective.ne hηl
    refine (side_cover hs' _ hi hl).resolve_right fun h => ?_
    have t := (fwd hα0.1 hα0.2).1 ((side_tri hbf hs x (.inl hα) hη).2 hα)
    have := (side_tri hbf' hs' (X'.M.a2 x') (ζ := f.fE α)
      (η := f.fE (X.M.edge (X.M.a1 (X.M.a0 x)))) (.inr (by rwa [X'.M.a2_a2]))
      (by rwa [X'.M.a0_a2])).1 (by simpa [X'.M.a0_a2] using t)
    exact side_disj hbf' hα' this
  have hζ : X.Inc (X.M.vtx x) ζ := (f.inc _ _).2 (hv ▸ hζ')
  have hζl : X.lineE ζ ≠ X.line x := fun h => hζl' (by rw [f.line, h, l'])
  rw [← side_tri hbf hs x (side_cover hs x hζ hζl) hη, fwd hζ hζl,
    side_tri hbf' hs' x' (side_cover hs' x' hζ' hζl') hη']

/-- **Corners are read on the skeleton** ((A1)–(A3)): a skeleton isomorphism carries the edge
after a flag `x` (the corner at its vertex) to the edge after one of the two flags of the image
edge at the image vertex. -/
theorem SkelIso.corner_map (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (hF : X.FourthLine) (hF' : X'.FourthLine) (f : SkelIso X X') (x : D)
    {x0 : D'} (hv : X'.M.vtx x0 = f.fV (X.M.vtx x)) (he : X'.M.edge x0 = f.fE (X.M.edge x)) :
    ∃ x', X'.M.vtx x' = f.fV (X.M.vtx x) ∧ X'.M.edge x' = f.fE (X.M.edge x) ∧
      X'.M.edge (X'.M.a1 x') = f.fE (X.M.edge (X.M.a1 x)) := by
  have hc := side_one (X := X) x
  obtain ⟨hci, hcl⟩ := side_line hs hc
  have l0 : X'.line x0 = f.fL (X.line x) := by rw [← lineE_edge, he, f.line]; rfl
  obtain ⟨x', hv', he', hc'⟩ : ∃ x', X'.M.vtx x' = f.fV (X.M.vtx x) ∧
      X'.M.edge x' = f.fE (X.M.edge x) ∧ X'.Side x' (f.fE (X.M.edge (X.M.a1 x))) := by
    rcases side_cover hs' x0 (by rw [hv]; exact (f.inc _ _).1 hci)
      (by rw [f.line, l0]; exact f.fL.injective.ne hcl) with h | h
    exacts [⟨x0, hv, he, h⟩, ⟨_, by rw [vtx_a2, hv], by rw [edge_a2, he], h⟩]
  refine ⟨x', hv', he', ?_⟩
  obtain ⟨j, hj, hjc⟩ := hc'
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [← hjc]; simp [phi_apply]
  exfalso
  obtain ⟨ζ', h1, h2⟩ := (between_iff hbf' x' (i := j + 1) (by omega) hj).2 (by omega)
  have s1 := (f.side_map hbf hbf' hs hs' hF hF' hv' he' hc ⟨j, hj, hjc⟩ (ζ := f.fE.symm ζ')
    (by simpa using (side_line hs' h1).1) (by simpa using (side_line hs' h1).2)).2
    (by simpa using h1)
  have s2 := (f.side_map hbf hbf' hs hs' hF hF' (x := X.M.a2 (X.phi x))
    (x' := X'.M.a2 ((X'.phi ^ (j + 1)) x')) (by simp [hv']) (by
      rw [edge_a2, edge_a2, hjc]; simp [phi_apply]) (α := X.M.edge x)
    (by simpa using side_back x le_rfl (one_lt_nu x))
    (by rw [← he']; exact side_back x' (by omega) hj) (ζ := f.fE.symm ζ')
    (by simpa using (side_line hs' h2).1) (by simpa using (side_line hs' h2).2)).2
    (by simpa using h2)
  exact absurd ((between_iff hbf x le_rfl (one_lt_nu x)).1 ⟨_, s1, by simpa using s2⟩)
    (lt_irrefl 1)

/-- **A skeleton isomorphism carries face paths to face paths** when every triangle has a fourth
line avoiding its vertices, at vertices of any multiplicity. -/
theorem path_map_gen (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (hF : X.FourthLine) (hF' : X'.FourthLine) (f : SkelIso X X')
    {e1 e e2 : X.M.Edge} (h : X.Path3 e1 e e2) : X'.Path3 (f.fE e1) (f.fE e) (f.fE e2) := by
  obtain ⟨d, rfl, rfl, rfl⟩ := h
  have hvw := noLoop hbf d
  obtain ⟨d0, hd0v, hd0e⟩ := (f.inc _ _).1 (⟨d, rfl, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge d))
  obtain ⟨x', hv', he', h1'⟩ := f.corner_map hbf hbf' hs hs' hF hF' d hd0v hd0e
  have hw' : X'.M.vtx (X'.M.a0 x') = f.fV (X.M.vtx (X.M.a0 d)) := by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
    rw [← he', inc_iff] at this
    exact (this.resolve_left fun h => hvw (f.fV.injective (h.trans hv'))).symm
  obtain ⟨z', hzv, hze, hz1⟩ := f.corner_map hbf hbf' hs hs' hF hF' (X.M.a0 d) hw'
    (by simp [he'])
  rcases (at_edge hbf').1 ⟨hzv.trans hw'.symm, by simp [hze, he']⟩ with rfl | rfl
  · exact ⟨x', h1', he', hz1⟩
  exfalso
  have t := f.tri_map hbf hbf' hs hs' hF ⟨d, rfl, rfl⟩ ⟨_, rfl, edge_a0 d⟩ hvw.symm
    (side_line hs (side_one d)).1 (side_line hs (side_one (X.M.a0 d))).1
    (side_line hs (side_one d)).2
    (by have := (side_line hs (side_one (X.M.a0 d))).2; rwa [X.line_a0] at this)
    ((side_tri hbf hs d (.inl (side_one d)) (side_one _)).2 (side_one d))
  have := (side_tri hbf' hs' (X'.M.a2 x') (ζ := f.fE (X.M.edge (X.M.a1 d)))
    (η := f.fE (X.M.edge (X.M.a1 (X.M.a0 d)))) (.inr (by rw [X'.M.a2_a2, ← h1']; exact side_one x'))
    (by rw [X'.M.a0_a2, ← hz1]; exact side_one _)).1 (by simpa [X'.M.a0_a2, hv', hw', he'] using t)
  exact side_disj hbf' (by rw [← h1']; exact side_one x') this

/-- **Full faithfulness without simplicity** (page 54, away from `III₆`). If every triangle of
both arrangements has a fourth line avoiding its vertices, every isomorphism of decomposed
skeleta comes from a unique isomorphism of the arrangements. -/
theorem full_of_fourth (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (hF : X.FourthLine) (hF' : X'.FourthLine) (f : SkelIso X X') :
    ∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d) :=
  (lift_iff hbf hbf' hs hs' f).2 fun _ _ _ => ⟨path_map_gen hbf hbf' hs hs' hF hF' f, fun h => by
    simpa [SkelIso.symm] using path_map_gen hbf' hbf hs' hs hF' hF f.symm h⟩

omit [Fintype D] [Fintype D'] in
/-- Having fourth lines is read on the skeleton. -/
theorem SkelIso.fourth_map (f : SkelIso X X') (hF : X.FourthLine) : X'.FourthLine := by
  intro a b c u v w h1 h2 h3 h4 h5 h6 h7
  have o : ∀ {u l}, X'.On u l → X.On (f.fV.symm u) (f.fL.symm l) := fun h => by
    rw [f.on_map]; simpa using h
  obtain ⟨Δ, n1, n2, n3⟩ := hF _ _ _ _ _ _ (o h1) (o h2) (o h3) (o h4) (o h5) (o h6)
    fun h => h7 (by simpa using f.on_map.1 h)
  exact ⟨f.fL Δ, fun h => n1 (by simpa using o h), fun h => n2 (by simpa using o h),
    fun h => n3 (by simpa using o h)⟩

/-- **Full faithfulness away from `III₆`.** If every triangle of a bigon-free arrangement has
a fourth line avoiding its vertices, every isomorphism of its decomposed skeleton with that of
another bigon-free arrangement comes from a unique isomorphism of the arrangements. -/
theorem full_of_fourth' (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (hF : X.FourthLine) (f : SkelIso X X') :
    ∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d) :=
  full_of_fourth hbf hbf' hs hs' hF (f.fourth_map hF) f

end Corners

/-! ### When a fourth line exists: triangles with a double vertex -/

section SimpleCorner

omit [Fintype D] in
/-- A line has a vertex other than any two given ones. -/
theorem third_vertex (hbf : BigonFree X.On) (l : L) (s t : X.M.Vtx) :
    ∃ q, X.On q l ∧ q ≠ s ∧ q ≠ t := by
  obtain ⟨q1, q2, q3, o1, o2, o3, n12, n13, n23⟩ := hbf l
  by_contra hc
  push Not at hc
  have k := fun q (hq : X.On q l) => (eq_or_ne q s).imp_right (hc q hq)
  rcases k _ o1 with rfl | rfl <;> rcases k _ o2 with h2 | h2 <;> rcases k _ o3 with h3 | h3 <;>
    simp_all

omit [Fintype D] in
/-- Through a vertex of `l` passes another line. -/
theorem other_line {q : X.M.Vtx} {l : L} (hq : X.On q l) : ∃ Δ, Δ ≠ l ∧ X.On q Δ := by
  obtain ⟨z, rfl, hz⟩ := hq
  obtain ⟨y, hyv, hyl⟩ := X.two z
  exact ⟨X.line y, fun h => hyl (h.trans hz.symm), y, hyv, rfl⟩

omit [Fintype D] in
/-- Two vertices on a line are avoided by some line. -/
theorem fourth_degen (hbf : BigonFree X.On) {u v : X.M.Vtx} {l : L} (hu : X.On u l)
    (hv : X.On v l) : ∃ Δ, ¬X.On u Δ ∧ ¬X.On v Δ := by
  obtain ⟨t, ht, htu, htv⟩ := third_vertex hbf l u v
  obtain ⟨Δ, hΔ, htΔ⟩ := other_line ht
  exact ⟨Δ, fun h => htu (meet_eq hΔ h hu htΔ ht).symm, fun h => htv (meet_eq hΔ h hv htΔ ht).symm⟩

omit [Fintype D] in
/-- **A triangle with a double vertex has a fourth line.** If only the two sides `a`, `b` pass
through the vertex `u` of the triangle `u, v, w`, some line passes through none of its
vertices. -/
theorem fourth_at (hbf : BigonFree X.On) {a b c : L} {u v w : X.M.Vtx} (h1 : X.On u a)
    (h2 : X.On u b) (h3 : X.On v b) (h4 : X.On v c) (h5 : X.On w c) (h6 : X.On w a)
    (h7 : ¬X.On u c) (hu : ∀ l, X.On u l → l = a ∨ l = b) :
    ∃ Δ, ¬X.On u Δ ∧ ¬X.On v Δ ∧ ¬X.On w Δ := by
  obtain ⟨q, hq, hqv, hqw⟩ := third_vertex hbf c v w
  obtain ⟨Δ, hΔ, hqΔ⟩ := other_line hq
  have hac : a ≠ c := fun h => h7 (h ▸ h1)
  have hbc : b ≠ c := fun h => h7 (h ▸ h2)
  refine ⟨Δ, fun h => ?_, fun h => hqv (meet_eq hΔ hqΔ hq h h4), fun h => hqw (meet_eq hΔ hqΔ hq h h5)⟩
  rcases hu Δ h with rfl | rfl
  · exact hqw (meet_eq hac hqΔ hq h6 h5)
  · exact hqv (meet_eq hbc hqΔ hq h3 h4)

variable (X) in
/-- Every (non-degenerate) triangle has a vertex through which only two of its sides pass. -/
def SimpleCorner : Prop := ∀ (a b c : L) (u v w : X.M.Vtx), a ≠ b → X.On u a → X.On u b →
  X.On v b → X.On v c → X.On w c → X.On w a → ¬X.On u c →
    (∀ l, X.On u l → l = a ∨ l = b) ∨ (∀ l, X.On v l → l = b ∨ l = c) ∨
      ∀ l, X.On w l → l = c ∨ l = a

omit [Fintype D] in
/-- Triangles with a double vertex have fourth lines: `SimpleCorner` implies `FourthLine`. A
triangle without a fourth line has three multiple vertices, as in the complete quadrangle. -/
theorem fourth_of_simpleCorner (hbf : BigonFree X.On) (H : X.SimpleCorner) : X.FourthLine := by
  intro a b c u v w h1 h2 h3 h4 h5 h6 h7
  have hac : a ≠ c := fun h => h7 (h ▸ h1)
  by_cases hab : a = b
  · subst hab
    have hvw : v = w := meet_eq hac h3 h4 h6 h5
    subst hvw
    obtain ⟨Δ, hu, hv⟩ := fourth_degen hbf h1 h3
    exact ⟨Δ, hu, hv, hv⟩
  have hbc : b ≠ c := fun h => h7 (h ▸ h2)
  have nva : ¬X.On v a := fun h => h7 (meet_eq hab h1 h2 h h3 ▸ h4)
  have nwb : ¬X.On w b := fun h => h7 (meet_eq hab h1 h2 h6 h ▸ h5)
  rcases H a b c u v w hab h1 h2 h3 h4 h5 h6 h7 with hu | hv | hw
  · exact fourth_at hbf h1 h2 h3 h4 h5 h6 h7 hu
  · obtain ⟨Δ, n1, n2, n3⟩ := fourth_at hbf h3 h4 h5 h6 h1 h2 nva hv
    exact ⟨Δ, n3, n1, n2⟩
  · obtain ⟨Δ, n1, n2, n3⟩ := fourth_at hbf h5 h6 h1 h2 h3 h4 nwb hw
    exact ⟨Δ, n2, n3, n1⟩

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

/-- **Full faithfulness when every triangle has a double vertex.** If every triangle of a
bigon-free arrangement has a vertex on exactly two lines (for instance a simple arrangement),
every isomorphism of its decomposed skeleton with that of another bigon-free arrangement comes
from a unique isomorphism of the arrangements. The complete quadrangle `III₆` is excluded. -/
theorem full_of_simpleCorner (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (H : X.SimpleCorner) (f : SkelIso X X') :
    ∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d) :=
  full_of_fourth' hbf hbf' hs hs' (fourth_of_simpleCorner hbf H) f

end SimpleCorner

end PseudolineMap

end Grothendieck.Folder80Maps3
