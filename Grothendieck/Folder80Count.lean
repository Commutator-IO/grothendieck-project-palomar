module

public import Mathlib
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Iterate

@[expose] public section


/-!
# Folder 80, page 9: the regions of the arrangement of nine curves

Page 9 draws, in a pencil circle, nine curves `Δ_A, Δ_A′, Δ_B, Δ_B′, Δ_C, Δ_C′, D_A, D_B, D_C`,
writes in each region its number of sides (`3`, `4`, `5`, primed for the regions « à l'infini »)
and counts

> triangles : 1 + 3 + 3 = 7, carrés : 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 = 24, pentagones : 3 + 3 = 6,

37 regions, whose side-sum `3·7 + 4·24 + 5·6 = 147` is odd (the reading, `80.modern.tex`,
« Un arrangement de neuf courbes »). This is finding `80-p9-region-count-rim-arcs`.

**What is the page's, what is the redraw's, what is ours.** The count and the labels are the
page's. The combinatorial data below are read off the machine redraw `80/drawings/01-3.tex`
(overlay-checked, centre confirmed by the editor in #151, not checked by a reader) by a script
of this pass: the curves are clipped by the drawn circle and intersected; every pair crosses
exactly once inside the disc, and the result is stable under the smoothing of the curves. The
data are

* `seq l`: the order in which the curve `l` crosses the eight others, from its end `s` to its
  end `t` (curves numbered `0 … 8` = `Δ_A, Δ_A′, Δ_B, Δ_B′, Δ_C, Δ_C′, D_A, D_B, D_C`);
* `rim`: the eighteen ends on the circle, counterclockwise.

Everything else is computed from these two lists. In the disc, the curve `l` is cut into nine
segments `0 … 8` by its crossings; a *dart* is a segment with a direction (`dart l j fwd`), or
one of the eighteen arcs of the rim, run counterclockwise. Which way `m` crosses `l` is read on
the rim (`startsRight`), and `nxt` follows the boundary of the region on the left of a dart,
turning left at each crossing and running along the rim at an end. The regions of the disc are
the cycles of `nxt`; `faces` lists them (46 lists), and `faces_cover`, `faces_nodup`,
`faces_cycle` check that they are exactly those cycles. The projective plane is the disc with
antipodal rim points glued; the ends are in antipodal order (`rim_antipodal`), so the region on
rim arc `k` is glued to the one on arc `k + 9`, and the two segments of each curve at the glued
ends become one edge: a glued face has `a + b − 2` sides, `a`, `b` the numbers of curve segments
of its two pieces (`projSides`).

* `proj_count`: 37 faces, 10 triangles, 21 quadrilaterals, 6 pentagons, side-sum
  `144 = 2 · 72`; `euler_proj`: `36 − 72 + 37 = 1`; `euler_disc`: `54 − 99 + 46 = 1`.
* `inner_count`: the 28 regions away from the rim are 7 triangles (the central `D_A D_B D_C`,
  `central_triangle`, and six others), 18 quadrilaterals, 3 pentagons; `rim_count`: the nine
  faces across the rim are 3 triangles, 3 quadrilaterals and 3 pentagons.
* `labels_rim`: the page's eighteen labels on the rim pieces (`pageRim`) are the projective side
  numbers, the two pieces of a face carrying the same digit, one primed.
* `page_count`: the page's rows are `7 = ` the inner triangles, `24 = ` the inner and rim
  quadrilaterals **and the three rim triangles**, `6 = ` the inner and rim pentagons; so the
  page's 7, 24, 6 is the projective count with the three rim triangles put among the
  quadrilaterals, and `147 = 144 + 3`. Each rim triangle is the gluing of a piece with three
  curve sides `Δ_X, Δ_X′, D` (four sides in the disc, the rim arc closing it) and a piece with
  two (`rim_triangle_pieces`); the page labels both pieces `3` and `3′`.
* `rim_arc_side`: counting the rim arc as a side of every face across the rim does not give the
  page's count either (it gives 7, 21, 6 and three hexagons), and the regions of the disc, rim arc
  counted, are 13 triangles, 24 quadrilaterals and 9 pentagons (`disc_count`).

Not formalised: the passage from the drawing to the two lists (a script on the redraw), and
that the data define a topological arrangement; the non-stretchability (a literature result).
-/

namespace Grothendieck.Folder80Count

/-- Crossing order of each curve, from its end `s` (read off the redraw). Curves:
`0 Δ_A, 1 Δ_A′, 2 Δ_B, 3 Δ_B′, 4 Δ_C, 5 Δ_C′, 6 D_A, 7 D_B, 8 D_C`. -/
def seq : List (List ℕ) :=
  [[1, 4, 3, 6, 5, 7, 2, 8], [0, 8, 3, 7, 4, 6, 2, 5], [3, 0, 5, 8, 1, 6, 4, 7],
    [2, 7, 5, 6, 0, 8, 4, 1], [6, 0, 8, 3, 7, 1, 2, 5], [3, 0, 7, 2, 8, 1, 6, 4],
    [4, 3, 0, 8, 7, 1, 2, 5], [3, 0, 5, 8, 6, 4, 1, 2], [0, 5, 2, 7, 6, 3, 4, 1]]

/-- The crossing order of the curve `l`. -/
def sq (l : ℕ) : List ℕ := seq.getD l []

/-- The eighteen ends on the rim, counterclockwise: `(curve, is the end t)`. -/
def rim : List (ℕ × Bool) :=
  [(8, true), (0, false), (1, false), (6, false), (4, false), (5, false), (7, false), (2, false),
    (3, false), (8, false), (0, true), (1, true), (6, true), (4, true), (5, true), (7, true),
    (2, true), (3, true)]

/-- Position of an end on the rim. -/
def pos (l : ℕ) (e : Bool) : ℕ := rim.idxOf (l, e)

/-- `x` lies strictly inside the counterclockwise rim arc from `a` to `b`. -/
def inArc (x a b : ℕ) : Bool :=
  decide (0 < (x + 18 - a) % 18) && decide ((x + 18 - a) % 18 < (b + 18 - a) % 18)

/-- The curve `m` starts on the right of `l` (so crosses it from right to left). -/
def startsRight (l m : ℕ) : Bool := inArc (pos m false) (pos l false) (pos l true)

/-- The dart on segment `j` of the curve `l`, forward or backward; darts `162 + k` are the rim
arcs. -/
def dart (l j : ℕ) (fwd : Bool) : ℕ := 18 * l + 2 * j + if fwd then 0 else 1

/-- The next dart on the boundary of the region on the left. -/
def nxt (d : ℕ) : ℕ :=
  if d < 162 then
    if d % 2 = 0 then
      if d % 18 / 2 = 8 then 162 + pos (d / 18) true
      else
        if startsRight (d / 18) ((sq (d / 18)).getD (d % 18 / 2) 0) then
          dart ((sq (d / 18)).getD (d % 18 / 2) 0)
            ((sq ((sq (d / 18)).getD (d % 18 / 2) 0)).idxOf (d / 18) + 1) true
        else
          dart ((sq (d / 18)).getD (d % 18 / 2) 0)
            ((sq ((sq (d / 18)).getD (d % 18 / 2) 0)).idxOf (d / 18)) false
    else
      if d % 18 / 2 = 0 then 162 + pos (d / 18) false
      else
        if startsRight (d / 18) ((sq (d / 18)).getD (d % 18 / 2 - 1) 0) then
          dart ((sq (d / 18)).getD (d % 18 / 2 - 1) 0)
            ((sq ((sq (d / 18)).getD (d % 18 / 2 - 1) 0)).idxOf (d / 18)) false
        else
          dart ((sq (d / 18)).getD (d % 18 / 2 - 1) 0)
            ((sq ((sq (d / 18)).getD (d % 18 / 2 - 1) 0)).idxOf (d / 18) + 1) true
  else
    if (rim.getD ((d - 162 + 1) % 18) (0, false)).2 then
      dart (rim.getD ((d - 162 + 1) % 18) (0, false)).1 8 false
    else dart (rim.getD ((d - 162 + 1) % 18) (0, false)).1 0 true

/-- Each curve crosses each other one exactly once in the disc. -/
theorem seq_simple : ∀ l < 9, (sq l).length = 8 ∧ (sq l).Nodup ∧ l ∉ sq l ∧ ∀ m ∈ sq l, m < 9 := by
  decide +kernel

/-- The ends are eighteen distinct points, in antipodal order: the end at `k + 9` is the other
end of the curve at `k`. -/
theorem rim_antipodal : rim.length = 18 ∧ rim.Nodup ∧ ∀ k < 9,
    (rim.getD (k + 9) (0, false)).1 = (rim.getD k (0, false)).1 := by
  decide +kernel

/-- The regions of the disc, as cycles of darts (computed, then checked below). -/
def faces : List (List ℕ) :=
  [[0, 20, 160, 162], [1, 163, 18], [2, 76, 158, 21], [3, 19, 164, 108, 74], [4, 64, 156, 77],
    [5, 75, 110, 62], [6, 114, 154, 65], [7, 63, 112], [8, 94, 132, 152, 115], [9, 113, 61, 92],
    [10, 130, 95], [11, 93, 59, 128], [12, 40, 97, 131], [13, 129, 57, 38], [14, 146, 99, 41],
    [15, 39, 55, 170, 144], [16, 172, 35, 101, 147], [17, 145, 171], [22, 70, 179, 161],
    [23, 159, 78, 68], [24, 140, 52, 178, 71], [25, 69, 80, 138], [26, 84, 50, 141],
    [27, 139, 82], [28, 120, 48, 85], [29, 83, 137, 118], [30, 46, 121], [31, 119, 135, 151, 44],
    [32, 102, 123, 47], [33, 45, 149, 100], [34, 173, 125, 103], [36, 56, 127, 168],
    [37, 169, 54], [42, 150, 133, 96], [43, 98, 148], [49, 122, 104, 87],
    [51, 86, 106, 176, 143], [53, 142, 177], [58, 91, 167, 126], [60, 111, 73, 166, 90],
    [66, 79, 157], [67, 155, 116, 136, 81], [72, 109, 165], [88, 175, 107], [89, 105, 124, 174],
    [117, 153, 134]]

/-- Every dart lies on exactly one listed region, and only darts are listed. -/
theorem faces_cover : (∀ d < 180, (faces.filter fun f => d ∈ f).length = 1) ∧
    ∀ f ∈ faces, ∀ d ∈ f, d < 180 := by
  decide +kernel

theorem faces_nodup : ∀ f ∈ faces, f.Nodup := by decide +kernel

/-- Each listed region is a cycle of `nxt`. -/
theorem faces_cycle : ∀ f ∈ faces, ∀ i < f.length,
    nxt (f.getD i 0) = f.getD ((i + 1) % f.length) 0 := by
  decide +kernel

/-- A listed region is closed under `nxt`, so it contains the whole orbit of each of its darts;
with `faces_cycle` and `faces_cover`, the listed regions are exactly the orbits. -/
theorem nxt_iterate_mem {f : List ℕ} (hf : f ∈ faces) {d : ℕ} (hd : d ∈ f) (n : ℕ) :
    nxt^[n] d ∈ f := by
  induction n generalizing d with
  | zero => exact hd
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    have hpos : 0 < f.length := by omega
    have h := faces_cycle f hf i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ hpos),
      Option.getD_some] at h
    rw [h]
    exact List.getElem_mem _

theorem faces_length : faces.length = 46 := by decide +kernel

/-- The number of curve segments on a region. -/
def chordSides (f : List ℕ) : ℕ := (f.filter fun d => decide (d < 162)).length

/-- The number of rim arcs on a region. -/
def rimArcs (f : List ℕ) : ℕ := (f.filter fun d => decide (162 ≤ d)).length

theorem rimArcs_le : ∀ f ∈ faces, rimArcs f ≤ 1 := by decide +kernel

/-- The regions away from the rim. -/
def inner : List (List ℕ) := faces.filter fun f => decide (rimArcs f = 0)

/-- The region of the disc on rim arc `k`. -/
def rimFace (k : ℕ) : List ℕ := (faces.find? fun f => decide (162 + k ∈ f)).getD []

/-- The number of sides of the face of the projective plane across rim arcs `k` and `k + 9`. -/
def projSides (k : ℕ) : ℕ := chordSides (rimFace k) + chordSides (rimFace (k + 9)) - 2

/-- The numbers of sides of the faces of the projective plane. -/
def projSizes : List ℕ := inner.map List.length ++ (List.range 9).map projSides

/-- The two pieces of a face across the rim are distinct regions, each with its rim arc. -/
theorem rimFace_spec : ∀ k < 18, rimFace k ∈ faces ∧ 162 + k ∈ rimFace k ∧
    rimArcs (rimFace k) = 1 := by
  decide +kernel

/-- **The projective count**: 37 faces, 10 triangles, 21 quadrilaterals, 6 pentagons, and the
side-sum is `144 = 2 · 72`, twice the number of edges. -/
theorem proj_count : projSizes.length = 37 ∧ projSizes.count 3 = 10 ∧ projSizes.count 4 = 21 ∧
    projSizes.count 5 = 6 ∧ projSizes.sum = 144 := by
  decide +kernel

/-- The number of crossings. -/
def numCross : ℕ := ((List.range 9).map fun l => (sq l).length).sum / 2

theorem numCross_eq : numCross = 36 := by decide +kernel

/-- Euler's relation `V − E + F = 1` in the projective plane, written `V + F = E + 1`: 36 vertices, `9 · 9 − 9 = 72` edges (the two end
segments of each curve are one edge), 37 faces. -/
theorem euler_proj : numCross + projSizes.length = (9 * 9 - 9) + 1 := by
  rw [numCross_eq, proj_count.1]

/-- Euler's relation `V − E + F = 1` in the disc, written `V + F = E + 1`: 36 crossings and 18 ends, 81 segments and 18 rim arcs, 46
regions. -/
theorem euler_disc : (numCross + rim.length) + faces.length = (9 * 9 + rim.length) + 1 := by
  rw [numCross_eq, rim_antipodal.1, faces_length]

/-- The regions away from the rim: 7 triangles, 18 quadrilaterals, 3 pentagons. -/
theorem inner_count : inner.length = 28 ∧ (inner.map List.length).count 3 = 7 ∧
    (inner.map List.length).count 4 = 18 ∧ (inner.map List.length).count 5 = 3 := by
  decide +kernel

/-- The nine faces across the rim: 3 triangles (arcs 0, 3, 6), 3 quadrilaterals (1, 4, 7), 3
pentagons (2, 5, 8). -/
theorem rim_count : (List.range 9).map projSides = [3, 4, 5, 3, 4, 5, 3, 4, 5] := by
  decide +kernel

/-- The central triangle is bounded by `D_A`, `D_B`, `D_C`. -/
theorem central_triangle : [117, 153, 134] ∈ inner ∧
    [117, 153, 134].map (· / 18) = [6, 8, 7] := by
  decide +kernel

/-- The curves along a region. -/
def curves (f : List ℕ) : List ℕ := (f.filter fun d => decide (d < 162)).map (· / 18)

/-- Each rim triangle is a piece `Δ_X Δ_X′ D` with three curve sides (four with its rim arc),
glued to a piece with two: `3 + 2 − 2 = 3`. -/
theorem rim_triangle_pieces :
    curves (rimFace 0) = [0, 1, 8] ∧ curves (rimFace 9) = [0, 8] ∧
    curves (rimFace 6) = [2, 3, 7] ∧ curves (rimFace 15) = [2, 7] ∧
    curves (rimFace 12) = [4, 5, 6] ∧ curves (rimFace 3) = [4, 6] := by
  decide +kernel

/-- The page's labels on the eighteen rim pieces, rim arc by rim arc: `(digit, primed)`. The 4′
are the thin wedges between `Δ_X` and `Δ_X′` (arcs 1, 7, 13); the thickened rim arcs are the
opposite arcs 10, 16, 4. Read off the redraw (label positions located in the regions). -/
def pageRim : List (ℕ × Bool) :=
  [(3, false), (4, true), (5, true), (3, true), (4, false), (5, false), (3, false), (4, true),
    (5, true), (3, true), (4, false), (5, false), (3, false), (4, true), (5, true), (3, true),
    (4, false), (5, false)]

/-- The page's labels at infinity are the projective numbers of sides: both pieces of a face
carry its number, one of them primed. -/
theorem labels_rim : ∀ k < 9, (pageRim.getD k (0, false)).1 = projSides k ∧
    (pageRim.getD (k + 9) (0, false)).1 = projSides k ∧
    (pageRim.getD k (0, false)).2 ≠ (pageRim.getD (k + 9) (0, false)).2 := by
  decide +kernel

/-- **The page's count.** Its rows are: the 7 inner triangles (`1 + 3 + 3`, the central one and
two orbits of three); 24 = the 18 inner quadrilaterals, the 3 rim quadrilaterals and the 3 rim
triangles; 6 = the 3 inner and 3 rim pentagons. So 7, 24, 6 is the projective count with the
three rim triangles among the quadrilaterals, and `147 = 144 + 3`. -/
theorem page_count :
    (inner.map List.length).count 3 = 1 + 3 + 3 ∧
    (inner.map List.length).count 4 + ((List.range 9).map projSides).count 4 +
      ((List.range 9).map projSides).count 3 = 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 ∧
    (inner.map List.length).count 5 + ((List.range 9).map projSides).count 5 = 3 + 3 ∧
    3 * 7 + 4 * 24 + 5 * 6 = projSizes.sum + 3 := by
  decide +kernel

/-- Counting the rim arc as a side of every face across the rim gives 7 triangles, 21
quadrilaterals, 6 pentagons and 3 hexagons: not the page's count. -/
theorem rim_arc_side :
    (inner.map List.length ++ (List.range 9).map fun k => projSides k + 1).count 3 = 7 ∧
    (inner.map List.length ++ (List.range 9).map fun k => projSides k + 1).count 4 = 21 ∧
    (inner.map List.length ++ (List.range 9).map fun k => projSides k + 1).count 5 = 6 ∧
    (inner.map List.length ++ (List.range 9).map fun k => projSides k + 1).count 6 = 3 := by
  decide +kernel

/-- The 46 regions of the disc, each rim arc counted as a side: 13 triangles, 24
quadrilaterals, 9 pentagons, side-sum `180` (the darts). -/
theorem disc_count : (faces.map List.length).count 3 = 13 ∧
    (faces.map List.length).count 4 = 24 ∧ (faces.map List.length).count 5 = 9 ∧
    (faces.map List.length).sum = 180 := by
  decide +kernel

end Grothendieck.Folder80Count
