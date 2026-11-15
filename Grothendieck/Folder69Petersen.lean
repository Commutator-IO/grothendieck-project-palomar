module

public import Mathlib
public import Grothendieck.Folder69

@[expose] public section


/-!
# Folder 69, pages 77 and 81: the « dodécaèdre gauche » of page 81

Page 77 counts « dodécaèdres gauches 2⁴·3³ = 36·12 = 36·6·2 » in the graph of the 27 lines and
draws one; page 81 is a figure alone: a central pentagon and five pentagons around it, fifteen
vertices labelled `ξ_{ij}` and twenty edges numbered `1 … 5`. This file proves the finite and
explicit parts of finding `69-petersen-hemidodecahedra-432`, on the figure as encoded in
`transcripts/69/drawings/05-1.json` (a machine redraw, not checked by a reader).

**Labels.** In the folder, for a base (a sixer) `ξ₁, …, ξ₆`, `ξ_{ij}` is the line meeting `ξ_i`
and `ξ′_j` (page 29: the triangle `(ξ₁, ξ′₂, ξ₁₂)`), the classical `c_{ij}`. The page writes
`ξ₅₁`, `ξ₄₁`, `ξ₅₃`, `ξ₃₁`, `ξ₅₂` with the indices in either order; we write each label as the
pair `(i, j)`, `i < j`. The vertex the transcription reads `ξ_{4,12}`, with `\uncertain{}`, is
left as a parameter `x`.

**The page's rule** (read off the figure by the edition, not stated on the page): an edge joins
two `ξ` with disjoint index pairs and carries the fifth index (`rule`).

* `rule_read`: the eighteen edges not at the uncertain vertex satisfy the rule as read;
  `forced`: at the uncertain vertex, the rule holds for its two edges (to `ξ₃₅`, numbered 1, and
  to `ξ₁₃`, numbered 5) iff `x = ξ₂₄`, among all `ξ_{ab}`, `1 ≤ a, b ≤ 5`.
* `antipodal`: with `x = ξ₂₄`, the boundary decagon carries the same labels and the same edge
  numbers at antipodal positions, and the five inner and the first five boundary vertices carry
  the ten labels once each: identifying antipodal boundary points is identifying equal labels.
* `quotient_adj`: after this identification the edges are the 15 pairs of disjoint index pairs:
  the 1-skeleton is the Kneser graph `K(5, 2)`, the Petersen graph (`petersen`);
  `petersen_lines`: in the graph `C` of the 27 lines (`Folder69.C`, indices shifted by one) the
  ten lines `c_{ij}`, `i, j ≤ 5`, induce exactly this graph (`petersenEmb : petersen ↪g C`).
* `hemi`: the six drawn pentagons become 5-cycles of the quotient, each of its 15 edges lies on
  exactly two of them, each vertex on three, and `10 − 15 + 6 = 1`: the face system of a
  hemi-dodecahedron.
* `pentagons_card`, `hemi_systems_card`, `drawn_is_system`: the Petersen graph has 12 pentagons
  and exactly two sets of six of them covering every edge twice; the drawn one is one of them.

Not formalised: the count `216 × 2 = 432` of hemi-dodecahedra in the 27-line graph, computed by
a program on the `C(27, 10)` ten-element subsets; a proof would need the transitivity of
`W(E₆)` on Petersen subgraphs, which is not proved here.
-/

namespace Grothendieck.Folder69Petersen

open Grothendieck.Folder69

/-- Two index pairs are disjoint. -/
def disj (p q : ℕ × ℕ) : Bool := p.1 != q.1 && p.1 != q.2 && p.2 != q.1 && p.2 != q.2

/-- The page's rule: an edge `ξ_p ξ_q` numbered `n` joins disjoint pairs and `n` is the fifth
index. -/
def rule (p q : ℕ × ℕ) (n : ℕ) : Bool :=
  disj p q && decide (1 ≤ n ∧ n ≤ 5) && !([p.1, p.2, q.1, q.2].contains n)

/-- The labels of the fifteen vertices of page 81, `x` at the uncertain one (vertex 7). Inner
pentagon `0 … 4`: `ξ₁₂, ξ₄₅, ξ₂₃, ξ₅₁, ξ₃₄`; boundary decagon `5 … 14`: `ξ₁₄, ξ₃₅, x, ξ₁₃,
ξ₂₅, ξ₄₁, ξ₅₃, ξ₂₄, ξ₃₁, ξ₅₂`. -/
def lab (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(1, 2), (4, 5), (2, 3), (1, 5), (3, 4), (1, 4), (3, 5), x, (1, 3), (2, 5), (1, 4), (3, 5),
    (2, 4), (1, 3), (2, 5)]

/-- The twenty edges with their numbers, as drawn. -/
def edges : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 3), (1, 2, 1), (2, 3, 4), (3, 4, 2), (4, 0, 5), (5, 6, 2), (6, 0, 4), (6, 7, 1),
    (7, 8, 5), (8, 1, 2), (8, 9, 4), (9, 10, 3), (10, 2, 5), (10, 11, 2), (11, 12, 1),
    (12, 3, 3), (13, 12, 5), (13, 14, 4), (14, 4, 1), (14, 5, 3)]

/-- The six pentagons, as drawn. -/
def faces : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 8, 7, 6], [1, 2, 10, 9, 8], [2, 3, 12, 11, 10], [3, 4, 14, 13, 12],
    [4, 0, 6, 5, 14]]

/-- The rule holds on an edge, for the labelling `lab x`. -/
def ruleAt (x : ℕ × ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  rule ((lab x).getD e.1 (0, 0)) ((lab x).getD e.2.1 (0, 0)) e.2.2

/-- The labels away from vertex 7 do not depend on `x`. -/
theorem lab_ne (x : ℕ × ℕ) {v : ℕ} (hv : v ≠ 7) : (lab x).getD v (0, 0) = (lab (0, 0)).getD v (0, 0) := by
  unfold lab
  rcases v with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|v <;> simp at hv ⊢

/-- The eighteen edges away from the uncertain vertex satisfy the rule as read. -/
theorem rule_read (x : ℕ × ℕ) : ∀ e ∈ edges, e.1 ≠ 7 → e.2.1 ≠ 7 → ruleAt x e = true := by
  intro e he h1 h2
  unfold ruleAt
  rw [lab_ne x h1, lab_ne x h2]
  exact (by decide +kernel : ∀ e ∈ edges, e.1 ≠ 7 → e.2.1 ≠ 7 →
    rule ((lab (0, 0)).getD e.1 (0, 0)) ((lab (0, 0)).getD e.2.1 (0, 0)) e.2.2 = true) e he h1 h2

/-- **The uncertain vertex is `ξ₂₄`.** Among all `ξ_{ab}`, `1 ≤ a, b ≤ 5`, the rule holds on
both edges at vertex 7 (to `ξ₃₅`, numbered 1, and to `ξ₁₃`, numbered 5) only for `ξ₂₄`. -/
theorem forced : ∀ a ∈ [1, 2, 3, 4, 5], ∀ b ∈ [1, 2, 3, 4, 5], a < b →
    ((ruleAt (a, b) (6, 7, 1) && ruleAt (a, b) (7, 8, 5)) = true ↔ (a, b) = (2, 4)) := by
  decide +kernel

/-- The labelling with `x = ξ₂₄`. -/
def lab24 : List (ℕ × ℕ) := lab (2, 4)

/-- The number carried by the edge joining `u` and `v`, if drawn. -/
def num (u v : ℕ) : ℕ :=
  ((edges.find? fun e => (e.1 == u && e.2.1 == v) || (e.1 == v && e.2.1 == u)).map
    fun e => e.2.2).getD 0

/-- With `x = ξ₂₄` all twenty edges satisfy the rule; the boundary decagon carries the same label
and the same edge number at antipodal positions; and vertices `0 … 9` carry the ten labels
`ξ_{ij}`, `1 ≤ i < j ≤ 5`, once each. -/
theorem antipodal : (∀ e ∈ edges, ruleAt (2, 4) e = true) ∧
    (∀ i < 5, lab24.getD (5 + i) (0, 0) = lab24.getD (10 + i) (0, 0)) ∧
    (∀ i < 5, num (5 + i) (6 + i) = num (10 + i) (if i = 4 then 5 else 11 + i) ∧
      num (5 + i) (6 + i) ≠ 0) ∧
    (lab24.take 10).Nodup ∧ ∀ p ∈ lab24, p.1 < p.2 ∧ 1 ≤ p.1 ∧ p.2 ≤ 5 := by
  decide +kernel

/-- The ten pairs `(i, j)`, `1 ≤ i < j ≤ 5`. -/
def prs : List (ℕ × ℕ) :=
  [(1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The label pairs of the drawn edges, after identification. -/
def qedges : List (ℕ × ℕ) := edges.map fun e => (prs.idxOf (lab24.getD e.1 (0, 0)),
  prs.idxOf (lab24.getD e.2.1 (0, 0)))

/-- **The quotient is the Petersen graph.** Two labels are joined by a drawn edge iff their index
pairs are disjoint, and the twenty drawn edges give fifteen edges. -/
theorem quotient_adj : (∀ i < 10, ∀ j < 10,
      (qedges.contains (i, j) || qedges.contains (j, i)) = disj (prs.getD i (0, 0)) (prs.getD j (0, 0))) ∧
    ((qedges.map fun e => (min e.1 e.2, max e.1 e.2)).dedup.length = 15) := by
  decide +kernel

/-- The Petersen graph, as the Kneser graph `K(5, 2)`: the pairs of `{1, …, 5}`, two joined when
disjoint. -/
def petersen : SimpleGraph (Fin 10) where
  Adj i j := disj (prs.getD i (0, 0)) (prs.getD j (0, 0)) = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel petersen.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-- The line `ξ_{ij} = c_{ij}` in `Folder69.C`, whose indices are `0 … 5` (shift by one). -/
def cLine (i : Fin 10) : Fin 27 :=
  ⟨(12 + pairs.idxOf ((prs.getD i (0, 0)).1 - 1, (prs.getD i (0, 0)).2 - 1)) % 27,
    Nat.mod_lt _ (by decide)⟩

theorem cLine_injective : Function.Injective cLine := by decide

/-- **The ten lines `ξ_{ij}` of the figure induce the Petersen graph in the graph of the 27
lines.** -/
theorem petersen_lines : ∀ i j : Fin 10, C.Adj (cLine i) (cLine j) ↔ petersen.Adj i j := by
  decide +kernel

/-- The induced embedding of the Petersen graph in the 27-line graph. -/
def petersenEmb : petersen ↪g C where
  toFun := cLine
  inj' := cLine_injective
  map_rel_iff' := (petersen_lines _ _)

/-- The drawn pentagons, on the quotient's vertices `0 … 9` (indices into `prs`). -/
def qfaces : List (List ℕ) := faces.map fun f => f.map fun v => prs.idxOf (lab24.getD v (0, 0))

/-- `{u, v}` is a side of the cyclic list `f`. -/
def side (f : List ℕ) (u v : ℕ) : Bool :=
  (List.range f.length).any fun k =>
    (f.getD k 0 == u && f.getD ((k + 1) % f.length) 0 == v) ||
      (f.getD k 0 == v && f.getD ((k + 1) % f.length) 0 == u)

/-- **A hemi-dodecahedron.** The six drawn pentagons become 5-cycles of the Petersen graph
(five distinct vertices, consecutive ones joined); each of the 15 edges is a side of exactly two
of them and each vertex lies on three; `V − E + F = 10 − 15 + 6 = 1`. -/
theorem hemi : qfaces.length = 6 ∧
    (∀ f ∈ qfaces, f.length = 5 ∧ f.Nodup ∧ ∀ k < 5,
      disj (prs.getD (f.getD k 0) (0, 0)) (prs.getD (f.getD ((k + 1) % 5) 0) (0, 0)) = true) ∧
    (∀ i < 10, ∀ j < 10, disj (prs.getD i (0, 0)) (prs.getD j (0, 0)) = true →
      (qfaces.filter fun f => side f i j).length = 2) ∧
    (∀ i < 10, (qfaces.filter fun f => f.contains i).length = 3) := by
  decide +kernel

/-- The number of edges of the Petersen graph. -/
theorem petersen_edges : ((List.range 10).flatMap fun i => (List.range 10).filter fun j =>
    i < j && disj (prs.getD i (0, 0)) (prs.getD j (0, 0))).length = 15 := by
  decide +kernel

/-! ### The two hemi-dodecahedra on a Petersen graph

Vertex sets are bit masks on `0 … 9`. A pentagon is a five-element set on which every vertex has
exactly two neighbours (the Petersen graph has girth 5, so such a set spans a 5-cycle and its
sides are its edges). -/

/-- Adjacency in the Petersen graph, on indices. -/
def adj (i j : ℕ) : Bool := disj (prs.getD i (0, 0)) (prs.getD j (0, 0))

/-- The vertices of a mask. -/
def verts (m : ℕ) : List ℕ := (List.range 10).filter fun i => m.testBit i

/-- A mask is a pentagon. -/
def isPent (m : ℕ) : Bool :=
  (verts m).length == 5 && (verts m).all fun i => ((verts m).filter (adj i)).length == 2

/-- The pentagons of the Petersen graph. -/
def pents : List ℕ := (List.range 1024).filter isPent

theorem pentagons_card : pents.length = 12 := by decide +kernel

/-- The edges of the Petersen graph. -/
def pedges : List (ℕ × ℕ) :=
  (List.range 10).flatMap fun i => ((List.range 10).filter fun j => i < j && adj i j).map (i, ·)

/-- A set of pentagons (a mask on `pents`) has six members and covers every edge twice. -/
def isHemi (s : ℕ) : Bool :=
  ((List.range 12).filter s.testBit).length == 6 &&
    pedges.all fun e => (((List.range 12).filter s.testBit).filter fun k =>
      (pents.getD k 0).testBit e.1 && (pents.getD k 0).testBit e.2).length == 2

/-- **Exactly two** systems of six pentagons cover every edge twice. -/
theorem hemi_systems_card : ((List.range 4096).filter isHemi).length = 2 := by decide +kernel

/-- The mask of a list of vertices. -/
def mask (f : List ℕ) : ℕ := (f.map fun i => 2 ^ i).sum

/-- The drawn face system is one of the two. -/
theorem drawn_is_system : ∃ s ∈ (List.range 4096).filter isHemi,
    ((List.range 12).filter s.testBit).map (pents.getD · 0) =
      (pents.filter fun m => (qfaces.map mask).contains m) ∧
    (qfaces.map mask).all pents.contains := by
  decide +kernel

end Grothendieck.Folder69Petersen
