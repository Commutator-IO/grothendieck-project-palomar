module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.GroupTheory.SpecificGroups.Alternating

@[expose] public section


/-!
# Folder 86, pages 18–32: the five trièdres of the icosahedron and the hemi-icosahedron

The modernised reading `transcripts/86/86.modern.tex` (« [Polyèdres réguliers] ») defines,
on the combinatorial icosahedron `Π` with antipodism `ι`, a permutation `ρ` of the fifteen
edge directions by « the side of the link pentagon of `s` opposite `t` » (pages 18–19), calls
its orbits the *trièdres distingués*, shows that `G = Aut Π` acts on the five trièdres by
even permutations with image `Alt_T` and kernel `⟨ι⟩` (pages 20–25), and rebuilds the
quotient `Π/ι` (the hemi-icosahedron) from the oriented five-set `T` (pages 26–32). These are
findings `86-combinatorial-five-triedres` and `86-hemi-icosahedron-five-set-model` of
`src/content/findings.ts`. Proving them says only that the statements hold as written here;
whether they stand in the literature is a separate question.

The model. Vertices are `Fin 12` with an explicit neighbour list (`nbrs`); `Adj` is the
adjacency, `other x y z` the third vertex of the other face on `{x, y}`, `anti` the vertex at
distance `3` (`anti_iff`). `G` is the group of adjacency-preserving bijections (`Aut`), with
no model-specific input: every automorphism is determined by the image of the flag `(0, 1, 2)`
(`eq_ext`), every flag is such an image (`mkAut`), so `Nat.card G = 120` (`card_aut`).

Trièdres. `rho0 (s, t)` is computed from adjacency only. `rho_cube`: `ρ³ = id` without fixed
point on directions; `rho_sq`: `ρ²(\bar a) = \overline{\{u, ι v\}}`. The table `colTab` labels
edges by `Fin 5`, and `col_eq_iff` shows that two edges carry the same label exactly when their
directions lie in the same `ρ`-orbit, so the labels are the trièdres. `col_inj_at`,
`col_surj_at`: each trièdre meets the five edges at a vertex once (`P(s) ≃ T`); each trièdre is
a perfect matching, and orthogonal edges are disjoint (`orthogonal_disjoint`). Page 23:
`face_triedres`, with the page's first direction `{u, v}` corrected to `{u, v₁}`
(`face_triedre_page_reading`).

The action. `permT : G →* Perm (Fin 5)` is defined from the action on edges and is a
homomorphism because automorphisms commute with `ρ` and `ι`. `permT_mem_alternating`: the
image is even; `permT_surjective`: it is all of `Alt_T`; `permT_eq_one_iff`: the kernel is
`{1, ι}` (page 25).

The hemi-icosahedron. `numb p` is the numbering of `T` given by a flag `p = (s, t, u)` (the
trièdres of the edges at `s`, read from `t` away from `u`; page 30). `numb_even`,
`numb_surjective`, `numb_eq_iff`: the numberings are the 60 even numberings, and two flags have
the same one iff they are equal or antipodal. `numb_sigma`: the flag involutions act by the
double transpositions of places `τ0`, `τ1`, `τ2`; `τ0`, `τ2` are those of page 31, and the
page's `σ₁` (`τ1'`) is `τ2 τ1 τ2`, the action on the numbering `numb ∘ fl2`
(`numb_sigma_page`). `page32`: the values and orders on page 32, and the page's label `σ₀σ₁`
for the value of `σ₀σ₂`. `incidence_dictionary`: same vertex, edge, face of `Π/ι` iff same
pentagon, same `(2, 2, 1)` partition, same three-element set. `vertex_pentagons`: a numbering
traces a vertex pentagon iff it is even (the dihedral group of the pentagon is even,
`dihedral_even`); `counts`: 6 pentagons, 15 partitions, all 10 three-element subsets.

All finite checks use `decide +kernel`, which the kernel checks.
-/

namespace Grothendieck.Folder86

/-! ## The combinatorial icosahedron -/

/-- Neighbours of each vertex: `0` and `11` are opposite poles, `1–5` and `6–10` the two
pentagons. -/
def nbrs : Fin 12 → List (Fin 12)
  | 0 => [1, 2, 3, 4, 5]
  | 1 => [0, 2, 5, 6, 7]
  | 2 => [0, 1, 3, 7, 8]
  | 3 => [0, 2, 4, 8, 9]
  | 4 => [0, 3, 5, 9, 10]
  | 5 => [0, 1, 4, 6, 10]
  | 6 => [1, 5, 7, 10, 11]
  | 7 => [1, 2, 6, 8, 11]
  | 8 => [2, 3, 7, 9, 11]
  | 9 => [3, 4, 8, 10, 11]
  | 10 => [4, 5, 6, 9, 11]
  | 11 => [6, 7, 8, 9, 10]

/-- Adjacency in the icosahedron. -/
def Adj (x y : Fin 12) : Prop := y ∈ nbrs x

instance : DecidableRel Adj := fun x y => inferInstanceAs (Decidable (y ∈ nbrs x))

theorem adj_symm : ∀ x y, Adj x y → Adj y x := by decide +kernel

theorem adj_irrefl : ∀ x, ¬ Adj x x := by decide +kernel

/-- An oriented triangle `(x, y, z)`: a flag (vertex `x`, edge `{x, y}`, face `{x, y, z}`). -/
def Tri (x y z : Fin 12) : Prop := Adj x y ∧ Adj x z ∧ Adj y z

instance (x y z : Fin 12) : Decidable (Tri x y z) := by unfold Tri; infer_instance

/-- The common neighbours of two vertices. -/
def common (x y : Fin 12) : List (Fin 12) :=
  (List.finRange 12).filter (fun z => decide (Adj x z) && decide (Adj y z))

/-- For a face `{x, y, z}`, the third vertex of the other face on the edge `{x, y}`. -/
def other (x y z : Fin 12) : Fin 12 :=
  ((common x y).filter (fun w => w ≠ z)).headD 0

theorem other_spec : ∀ x y z, Tri x y z →
    Adj x (other x y z) ∧ Adj y (other x y z) ∧ other x y z ≠ z := by decide +kernel

theorem other_uniq : ∀ x y z w, Tri x y z → Adj x w → Adj y w → w ≠ z →
    w = other x y z := by decide +kernel

/-- The antipodism: the vertex at distance `3` (`anti_iff`). -/
def anti : Fin 12 → Fin 12 := ![11, 9, 10, 6, 7, 8, 3, 4, 5, 1, 2, 0]

/-- `anti x` is the only vertex that is neither `x`, nor a neighbour of `x`, nor a neighbour
of a neighbour of `x`. -/
theorem anti_iff : ∀ x y, y = anti x ↔ (y ≠ x ∧ ¬ Adj x y ∧ ∀ z, Adj x z → ¬ Adj z y) := by
  decide +kernel

theorem anti_anti : ∀ x, anti (anti x) = x := by decide +kernel

theorem adj_anti : ∀ x y, Adj x y → Adj (anti x) (anti y) := by decide +kernel

/-! ## Automorphisms -/

/-- The automorphism group `G` of the icosahedron. -/
abbrev Aut := Adj ≃r Adj

/-- An automorphism is determined on a face by `other`. -/
theorem map_other (g : Aut) {x y z : Fin 12} (h : Tri x y z) :
    g (other x y z) = other (g x) (g y) (g z) := by
  obtain ⟨h1, h2, h3⟩ := other_spec x y z h
  exact other_uniq _ _ _ _ ⟨g.map_rel_iff.2 h.1, g.map_rel_iff.2 h.2.1, g.map_rel_iff.2 h.2.2⟩
    (g.map_rel_iff.2 h1) (g.map_rel_iff.2 h2) (fun e => h3 (g.injective e))

theorem map_anti (g : Aut) (x : Fin 12) : g (anti x) = anti (g x) := by
  obtain ⟨h1, h2, h3⟩ := (anti_iff x (anti x)).1 rfl
  refine (anti_iff (g x) (g (anti x))).2 ⟨fun e => h1 (g.injective e),
    fun e => h2 (g.map_rel_iff.1 e), fun z hz e => ?_⟩
  exact h3 (g.symm z) (by simpa using g.map_rel_iff.1 (by simpa using hz))
    (g.map_rel_iff.1 (by simpa using e))

/-- The automorphism sending the flag `(0, 1, 2)` to `(x, y, z)`, computed vertex by vertex
with `other`. -/
def ext (x y z : Fin 12) (v : Fin 12) : Fin 12 :=
  let v5 := other x y z
  let v3 := other x z y
  let v4 := other x v3 z
  let v6 := other y v5 x
  let v7 := other y z x
  let v8 := other z v3 x
  let v9 := other v3 v4 x
  let v10 := other v4 v5 x
  let v11 := other v6 v7 y
  ![x, y, z, v3, v4, v5, v6, v7, v8, v9, v10, v11] v

/-- An automorphism is determined by the image of one flag. -/
theorem eq_ext (g : Aut) : ⇑g = ext (g 0) (g 1) (g 2) := by
  have h5 : g 5 = other (g 0) (g 1) (g 2) := by
    rw [← map_other g (by decide)]; rfl
  have h3 : g 3 = other (g 0) (g 2) (g 1) := by
    rw [← map_other g (by decide)]; rfl
  have h4 : g 4 = other (g 0) (g 3) (g 2) := by
    rw [← map_other g (by decide)]; rfl
  have h6 : g 6 = other (g 1) (g 5) (g 0) := by
    rw [← map_other g (by decide)]; rfl
  have h7 : g 7 = other (g 1) (g 2) (g 0) := by
    rw [← map_other g (by decide)]; rfl
  have h8 : g 8 = other (g 2) (g 3) (g 0) := by
    rw [← map_other g (by decide)]; rfl
  have h9 : g 9 = other (g 3) (g 4) (g 0) := by
    rw [← map_other g (by decide)]; rfl
  have h10 : g 10 = other (g 4) (g 5) (g 0) := by
    rw [← map_other g (by decide)]; rfl
  have h11 : g 11 = other (g 6) (g 7) (g 1) := by
    rw [← map_other g (by decide)]; rfl
  funext v
  fin_cases v <;> simp only [ext] <;> first
    | rfl
    | (simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]; simp_all)

/-- Inverse of a map `Fin 12 → Fin 12`, by search. -/
def inv12 (f : Fin 12 → Fin 12) (v : Fin 12) : Fin 12 :=
  ((List.finRange 12).filter (fun w => f w = v)).headD 0

theorem ext_adj_iff : ∀ x y z, Tri x y z → ∀ v w, Adj (ext x y z v) (ext x y z w) ↔ Adj v w := by
  decide +kernel

theorem ext_left_inv : ∀ x y z, Tri x y z → ∀ v, inv12 (ext x y z) (ext x y z v) = v := by
  decide +kernel

theorem ext_right_inv : ∀ x y z, Tri x y z → ∀ v, ext x y z (inv12 (ext x y z) v) = v := by
  decide +kernel

/-- For every flag `(x, y, z)` there is an automorphism sending `(0, 1, 2)` to it. -/
def mkAut (x y z : Fin 12) (h : Tri x y z) : Aut where
  toFun := ext x y z
  invFun := inv12 (ext x y z)
  left_inv := ext_left_inv x y z h
  right_inv := ext_right_inv x y z h
  map_rel_iff' := ext_adj_iff x y z h _ _

theorem mkAut_apply (x y z : Fin 12) (h : Tri x y z) : ⇑(mkAut x y z h) = ext x y z := rfl

theorem tri_zero : Tri 0 1 2 := by decide

theorem eq_mkAut (g : Aut) : g = mkAut (g 0) (g 1) (g 2)
    ⟨g.map_rel_iff.2 tri_zero.1, g.map_rel_iff.2 tri_zero.2.1, g.map_rel_iff.2 tri_zero.2.2⟩ :=
  RelIso.ext (congrFun (eq_ext g))

/-- The antipodism as an automorphism. -/
def antiAut : Aut where
  toFun := anti
  invFun := anti
  left_inv := anti_anti
  right_inv := anti_anti
  map_rel_iff' := fun {a b} => ⟨fun h => by simpa [anti_anti] using adj_anti _ _ h,
    adj_anti a b⟩

/-! ## The permutation `ρ` of the edge directions (pages 18–19) -/

/-- `ρ₀(s, t)`: with `u, v` the third vertices of the two faces on `{s, t}`, the side
`{Π_{s,u}, Π_{s,v}}` of the link pentagon of `s` opposite `t`. -/
def rho0 (p : Fin 12 × Fin 12) : Fin 12 × Fin 12 :=
  let u := (common p.1 p.2).headD 0
  let v := (common p.1 p.2).getD 1 0
  (other p.1 u p.2, other p.1 v p.2)

/-- Equality of unordered pairs. -/
def UEq (p q : Fin 12 × Fin 12) : Prop := (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)

instance (p q : Fin 12 × Fin 12) : Decidable (UEq p q) := by unfold UEq; infer_instance

/-- The antipodal pair. -/
def antiP (p : Fin 12 × Fin 12) : Fin 12 × Fin 12 := (anti p.1, anti p.2)

/-- Two edges have the same direction: equal, or antipodal, as unordered pairs. -/
def SameDir (p q : Fin 12 × Fin 12) : Prop := UEq p q ∨ UEq p (antiP q)

instance (p q : Fin 12 × Fin 12) : Decidable (SameDir p q) := by unfold SameDir; infer_instance

def IsEdge (p : Fin 12 × Fin 12) : Prop := Adj p.1 p.2

instance (p : Fin 12 × Fin 12) : Decidable (IsEdge p) := by unfold IsEdge; infer_instance

/-- `ρ₀(s, t)` does not depend on which of the two faces is called `u`. -/
theorem rho0_choice : ∀ s t u, Tri s t u →
    UEq (rho0 (s, t)) (other s u t, other s (other s t u) t) := by decide +kernel

theorem rho0_edge : ∀ p, IsEdge p → IsEdge (rho0 p) := by decide +kernel

/-- Starting from `t` instead of `s` gives the antipodal edge (page 18). -/
theorem rho0_swap : ∀ s t, Adj s t → UEq (rho0 (t, s)) (antiP (rho0 (s, t))) := by
  decide +kernel

/-- `ρ₀` passes to directions. -/
theorem rho0_sameDir : ∀ p q, IsEdge p → SameDir p q → SameDir (rho0 p) (rho0 q) := by
  decide +kernel

/-- `ρ³ = id`, without fixed point (pages 18–19). -/
theorem rho_cube : ∀ p, IsEdge p → SameDir (rho0 (rho0 (rho0 p))) p ∧ ¬ SameDir (rho0 p) p := by
  decide +kernel

/-- `ρ²(\bar a) = \overline{\{u, ι v\}}` (page 19), for either labelling of `u, v`. -/
theorem rho_sq : ∀ s t u, Tri s t u →
    SameDir (rho0 (rho0 (s, t))) (u, anti (other s t u)) := by decide +kernel

/-! ## The five trièdres (pages 18–20) -/

/-- A labelling of the edges by `Fin 5`. It is not a definition of the trièdres:
`col_eq_iff` shows that two edges have the same label exactly when their directions are
in the same `ρ`-orbit, so the labels name the five orbits. -/
def colTab : Fin 12 → Fin 12 → Fin 5 := ![![0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0],
  ![0, 0, 3, 0, 0, 2, 1, 4, 0, 0, 0, 0],
  ![1, 3, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0],
  ![2, 0, 4, 0, 0, 0, 0, 0, 3, 1, 0, 0],
  ![3, 0, 0, 0, 0, 1, 0, 0, 0, 4, 2, 0],
  ![4, 2, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 4, 2],
  ![0, 4, 2, 0, 0, 0, 0, 0, 1, 0, 0, 3],
  ![0, 0, 0, 3, 0, 0, 0, 1, 0, 2, 0, 4],
  ![0, 0, 0, 1, 4, 0, 0, 0, 2, 0, 3, 0],
  ![0, 0, 0, 0, 2, 0, 4, 0, 0, 3, 0, 1],
  ![0, 0, 0, 0, 0, 0, 2, 3, 4, 0, 1, 0]]

/-- The trièdre of an edge. -/
def col (p : Fin 12 × Fin 12) : Fin 5 := colTab p.1 p.2

/-- `q` lies in the trièdre of `p`: its direction is that of `p`, `ρ p` or `ρ² p`. -/
def SameTri (p q : Fin 12 × Fin 12) : Prop :=
  SameDir q p ∨ SameDir q (rho0 p) ∨ SameDir q (rho0 (rho0 p))

instance (p q : Fin 12 × Fin 12) : Decidable (SameTri p q) := by unfold SameTri; infer_instance

/-- The labels are the `ρ`-orbits of directions: five orbits of three directions. -/
theorem col_eq_iff : ∀ p q, IsEdge p → IsEdge q → (col p = col q ↔ SameTri p q) := by
  decide +kernel

/-- Each trièdre meets the five edges at a vertex once (page 20, corollary `P(s) ≃ T`). -/
theorem col_inj_at : ∀ s t t', Adj s t → Adj s t' → colTab s t = colTab s t' → t = t' := by
  decide +kernel

theorem col_surj_at : ∀ s c, ∃ t, Adj s t ∧ colTab s t = c := by decide +kernel

/-- Two orthogonal edges (same trièdre, different directions) have no common vertex
(page 20). With `col_inj_at`, each trièdre is a perfect matching of six edges. -/
theorem orthogonal_disjoint : ∀ p q, IsEdge p → IsEdge q → col p = col q → ¬ SameDir p q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by decide +kernel

/-- Page 23 a): for a face `{u, v, w}` with `u₁, v₁, w₁` the third vertices across
`{v, w}, {w, u}, {u, v}`, the directions `{u, v₁}, {v, w₁}, {w, u₁}` form a trièdre and
`{u, w₁}, {v, u₁}, {w, v₁}` another; b) these two and the trièdres of the three sides are
five distinct trièdres. -/
theorem face_triedres : ∀ u v w, Tri u v w →
    let u₁ := other v w u; let v₁ := other w u v; let w₁ := other u v w
    (colTab u v₁ = colTab v w₁ ∧ colTab v w₁ = colTab w u₁) ∧
    (colTab u w₁ = colTab v u₁ ∧ colTab v u₁ = colTab w v₁) ∧
    [colTab v w, colTab w u, colTab u v, colTab u v₁, colTab u w₁].Nodup := by
  decide +kernel

/-- The first triple as the page reads it, with `{u, v}` for `{u, v₁}`, is not a trièdre:
`{u, v}` and `{v, w₁}` never have the same trièdre. -/
theorem face_triedre_page_reading : ∀ u v w, Tri u v w →
    colTab u v ≠ colTab v (other u v w) := by decide +kernel

/-! ## The action of `G` on the trièdres -/

/-- Image of a pair under an automorphism. -/
def gP (g : Aut) (p : Fin 12 × Fin 12) : Fin 12 × Fin 12 := (g p.1, g p.2)

theorem head_tri : ∀ s t, Adj s t → Tri s t ((common s t).headD 0) := by decide +kernel

theorem getD_eq : ∀ s t, Adj s t → (common s t).getD 1 0 = other s t ((common s t).headD 0) := by
  decide +kernel

theorem tri_rot : ∀ x y z, Tri x y z → Tri x z y ∧ Tri x (other x y z) y := by decide +kernel

theorem map_tri (g : Aut) {x y z : Fin 12} (h : Tri x y z) : Tri (g x) (g y) (g z) :=
  ⟨g.map_rel_iff.2 h.1, g.map_rel_iff.2 h.2.1, g.map_rel_iff.2 h.2.2⟩

theorem map_rho0 (g : Aut) (p : Fin 12 × Fin 12) (hp : IsEdge p) :
    UEq (gP g (rho0 p)) (rho0 (gP g p)) := by
  obtain ⟨s, t⟩ := p
  have hu := head_tri s t hp
  set u := (common s t).headD 0
  have e1 : rho0 (s, t) = (other s u t, other s (other s t u) t) := by
    simp only [rho0]; rw [getD_eq s t hp]
  have hg := rho0_choice (g s) (g t) (g u) (map_tri g hu)
  rw [e1]
  have h1 := map_other g (tri_rot _ _ _ hu).1
  have h2 := map_other g (tri_rot _ _ _ hu).2
  have h3 := map_other g hu
  simp only [gP] at hg ⊢
  rw [h1, h2, h3]
  rcases hg with ⟨a, b⟩ | ⟨a, b⟩
  exacts [Or.inl ⟨a.symm, b.symm⟩, Or.inr ⟨b.symm, a.symm⟩]

theorem sameDir_trans' : ∀ a, IsEdge a → ∀ b, SameDir a b → ∀ c, SameDir b c →
    SameDir a c := by decide +kernel

theorem sameDir_trans (a b c : Fin 12 × Fin 12) (ha : IsEdge a) (_ : IsEdge b)
    (h1 : SameDir a b) (h2 : SameDir b c) : SameDir a c := sameDir_trans' a ha b h1 c h2

theorem sameDir_symm : ∀ a b, IsEdge a → SameDir a b → SameDir b a := by decide +kernel

theorem sameDir_of_ueq : ∀ a b, UEq a b → SameDir a b := fun _ _ h => Or.inl h

theorem map_sameDir (g : Aut) {a b : Fin 12 × Fin 12} (h : SameDir a b) :
    SameDir (gP g a) (gP g b) := by
  simp only [SameDir, UEq, antiP, gP] at h ⊢
  rw [← map_anti, ← map_anti]
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [h1, h2]

theorem isEdge_map (g : Aut) {p : Fin 12 × Fin 12} (h : IsEdge p) : IsEdge (gP g p) :=
  g.map_rel_iff.2 h

theorem map_sameTri (g : Aut) {p q : Fin 12 × Fin 12} (hp : IsEdge p) (hq : IsEdge q)
    (h : SameTri p q) : SameTri (gP g p) (gP g q) := by
  have hp1 := rho0_edge p hp
  have hp2 := rho0_edge _ hp1
  have gq := isEdge_map g hq
  have m1 := sameDir_of_ueq _ _ (map_rho0 g p hp)
  have m2 := sameDir_of_ueq _ _ (map_rho0 g _ hp1)
  have m3 := rho0_sameDir _ _ (isEdge_map g hp1) m1
  rcases h with h | h | h
  · exact Or.inl (map_sameDir g h)
  · exact Or.inr (Or.inl (sameDir_trans _ _ _ gq (isEdge_map g hp1) (map_sameDir g h) m1))
  · exact Or.inr (Or.inr (sameDir_trans _ _ _ gq (isEdge_map g hp2) (map_sameDir g h)
      (sameDir_trans _ _ _ (isEdge_map g hp2) (rho0_edge _ (isEdge_map g hp1)) m2 m3)))

/-- A vertex adjacent to `0` in each trièdre. -/
def nb0 : Fin 5 → Fin 12 := ![1, 2, 3, 4, 5]

theorem nb0_spec : ∀ c, IsEdge (0, nb0 c) ∧ col (0, nb0 c) = c := by decide

/-- The permutation of the trièdres induced by an automorphism. -/
def actT (g : Aut) (c : Fin 5) : Fin 5 := col (gP g (0, nb0 c))

theorem col_map (g : Aut) {p : Fin 12 × Fin 12} (hp : IsEdge p) :
    col (gP g p) = actT g (col p) := by
  obtain ⟨h0, hc⟩ := nb0_spec (col p)
  have : SameTri p (0, nb0 (col p)) := (col_eq_iff _ _ hp h0).1 hc.symm
  exact ((col_eq_iff _ _ (isEdge_map g hp) (isEdge_map g h0)).2
    (map_sameTri g hp h0 this))

theorem actT_mul (g h : Aut) (c : Fin 5) : actT (g * h) c = actT g (actT h c) := by
  simpa [actT, gP] using col_map g (isEdge_map h (nb0_spec c).1)

theorem actT_one (c : Fin 5) : actT 1 c = c := (nb0_spec c).2

/-- The homomorphism `G → 𝔖_T` (page 22). -/
def permT : Aut →* Equiv.Perm (Fin 5) where
  toFun g :=
    { toFun := actT g
      invFun := actT g⁻¹
      left_inv := fun c => by rw [← actT_mul, inv_mul_cancel, actT_one]
      right_inv := fun c => by rw [← actT_mul, mul_inv_cancel, actT_one] }
  map_one' := Equiv.ext actT_one
  map_mul' g h := Equiv.ext (actT_mul g h)

theorem permT_apply (g : Aut) (c : Fin 5) : permT g c = actT g c := rfl

/-! ## Kernel and image of `G → 𝔖_T` (pages 23–25) -/

theorem ext_zero : ∀ v, ext 0 1 2 v = v := by decide

theorem ext_anti : ∀ v, ext (anti 0) (anti 1) (anti 2) v = anti v := by decide +kernel

theorem permT_antiAut : permT antiAut = 1 := by
  ext c; revert c; decide +kernel

theorem kernel_aux : ∀ x y z, Tri x y z → (∀ c, colTab x (ext x y z (nb0 c)) = c) →
    (x = 0 ∧ y = 1 ∧ z = 2) ∨ (x = anti 0 ∧ y = anti 1 ∧ z = anti 2) := by decide +kernel

/-- Page 25: the kernel of `G → 𝔖_T` is `{1, ι}`. -/
theorem permT_eq_one_iff (g : Aut) : permT g = 1 ↔ g = 1 ∨ g = antiAut := by
  constructor
  · intro h
    have hc : ∀ c, colTab (g 0) (ext (g 0) (g 1) (g 2) (nb0 c)) = c := fun c => by
      have e := congrFun (eq_ext g) (nb0 c)
      have := Equiv.congr_fun h c
      simp only [permT_apply, actT, gP, col, Equiv.Perm.coe_one, id] at this
      rwa [e] at this
    rcases kernel_aux _ _ _ (map_tri g tri_zero) hc with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · left; apply RelIso.ext; intro v
      rw [congrFun (eq_ext g) v, a, b, c, ext_zero]; rfl
    · right; apply RelIso.ext; intro v
      rw [congrFun (eq_ext g) v, a, b, c, ext_anti]; rfl
  · rintro (rfl | rfl)
    exacts [map_one _, permT_antiAut]

theorem sign_aux : ∀ x y z (h : Tri x y z), Equiv.Perm.sign (permT (mkAut x y z h)) = 1 := by
  decide +kernel

/-- Pages 20–22: `G` acts on `T` by even permutations. -/
theorem permT_mem_alternating (g : Aut) : permT g ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, eq_mkAut g]
  exact sign_aux _ _ _ _

/-- The flags `(x, y, z)` of the icosahedron, as a list. -/
def triList : List (Fin 12 × Fin 12 × Fin 12) :=
  ((List.finRange 12).flatMap fun x => (List.finRange 12).flatMap fun y =>
    (List.finRange 12).map fun z => (x, y, z)).filter fun p => decide (Tri p.1 p.2.1 p.2.2)

theorem mem_triList (p : Fin 12 × Fin 12 × Fin 12) (h : p ∈ triList) :
    Tri p.1 p.2.1 p.2.2 := by
  simpa [triList] using (List.mem_filter.1 h).2

/-- The permutation of `T` induced by the automorphism sending `(0, 1, 2)` to `p`. -/
def permF (p : Fin 12 × Fin 12 × Fin 12) : Equiv.Perm (Fin 5) :=
  if h : Tri p.1 p.2.1 p.2.2 then permT (mkAut _ _ _ h) else 1

theorem card_image_permF : (triList.map permF).toFinset.card = 60 := by decide +kernel

/-- Page 25: `G → Alt_T` is onto. -/
theorem permT_surjective (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ g, permT g = σ := by
  classical
  set S := (triList.map permF).toFinset
  set A := (Finset.univ : Finset (Equiv.Perm (Fin 5))).filter (· ∈ alternatingGroup (Fin 5))
  have hSA : S ⊆ A := by
    intro τ hτ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hτ)
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, permF,
      dite_eq_left (mem_triList p hp)]
    exact permT_mem_alternating _
  have hA : A.card = 60 := by
    have h1 := card_alternatingGroup (α := Fin 5)
    rw [Fintype.card_fin, show (5 : ℕ).factorial / 2 = 60 by decide] at h1
    rw [← h1, Fintype.card_subtype]
  have hS : S = A := Finset.eq_of_subset_of_card_le hSA (by rw [hA, card_image_permF])
  have : σ ∈ S := by rw [hS]; simpa [A] using hσ
  obtain ⟨p, hp, e⟩ := List.mem_map.1 (List.mem_toFinset.1 this)
  refine ⟨mkAut _ _ _ (mem_triList p hp), ?_⟩
  rw [← e, permF, dite_eq_left (mem_triList p hp)]

/-- The automorphisms correspond to the `120` flags (`card_flags`). -/
def autEquivFlag : Aut ≃ {p : Fin 12 × Fin 12 × Fin 12 // Tri p.1 p.2.1 p.2.2} where
  toFun g := ⟨(g 0, g 1, g 2), map_tri g tri_zero⟩
  invFun p := mkAut _ _ _ p.2
  left_inv g := (eq_mkAut g).symm
  right_inv _ := rfl

theorem card_flags :
    Fintype.card {p : Fin 12 × Fin 12 × Fin 12 // Tri p.1 p.2.1 p.2.2} = 120 := by
  decide +kernel

theorem card_aut : Nat.card Aut = 120 := by
  rw [Nat.card_congr autEquivFlag, Nat.card_eq_fintype_card, card_flags]

/-! ## The hemi-icosahedron from the oriented five-set (pages 26–32) -/

/-- The numbering of `T` attached to a flag `(s, t, u)` (page 30): the trièdres of the five
edges at `s`, read around `s` from `t`, in the direction away from `u`. With `v` the other
face on `{s, t}`, these edges go to `t, v, Π_{s,v}, Π_{s,u}, u`. -/
def numb (p : Fin 12 × Fin 12 × Fin 12) : Fin 5 → Fin 5 :=
  ![colTab p.1 p.2.1, colTab p.1 (other p.1 p.2.1 p.2.2),
    colTab p.1 (other p.1 (other p.1 p.2.1 p.2.2) p.2.1),
    colTab p.1 (other p.1 p.2.2 p.2.1), colTab p.1 p.2.2]

/-- The numbering is natural: an automorphism acts on it through `G → 𝔖_T`. -/
theorem numb_map (g : Aut) {s t u : Fin 12} (h : Tri s t u) :
    numb (g s, g t, g u) = actT g ∘ numb (s, t, u) := by
  obtain ⟨hv1, -, -⟩ := other_spec s t u h
  have hsv := (tri_rot s t u h).2
  have hsu := (tri_rot s t u h).1
  obtain ⟨a1, -, -⟩ := other_spec _ _ _ hsv
  obtain ⟨a2, -, -⟩ := other_spec _ _ _ hsu
  have e1 := map_other g h
  have e2 := map_other g hsv
  have e3 := map_other g hsu
  have cm : ∀ x, Adj s x → colTab (g s) (g x) = actT g (colTab s x) := fun x hx =>
    col_map g (p := (s, x)) hx
  funext k
  simp only [numb, Function.comp]
  rw [← e1, ← e2, ← e3]
  fin_cases k
  exacts [cm _ h.1, cm _ hv1, cm _ a1, cm _ a2, cm _ h.2.1]

/-- The reversal of places `(a₁, a₂, a₃, a₄, a₅) ↦ (a₁, a₅, a₄, a₃, a₂)`. -/
def w0 : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 2 3

theorem numb_base : numb (0, 1, 2) = ⇑w0 := by decide +kernel

/-- The flag `g (0, 1, 2)`. -/
def flagOf (g : Aut) : Fin 12 × Fin 12 × Fin 12 := (g 0, g 1, g 2)

theorem numb_flagOf (g : Aut) : numb (flagOf g) = ⇑(permT g * w0) := by
  rw [flagOf, numb_map g tri_zero, numb_base]; rfl

theorem flagOf_mkAut (p : Fin 12 × Fin 12 × Fin 12) (h : Tri p.1 p.2.1 p.2.2) :
    flagOf (mkAut _ _ _ h) = p := rfl

theorem flagOf_mem (g : Aut) : flagOf g ∈ triList := by
  simp only [triList, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and, decide_eq_true_eq]
  exact ⟨⟨g 0, g 1, g 2, rfl⟩, map_tri g tri_zero⟩

theorem flagOf_injective : Function.Injective flagOf := fun g h e => by
  simp only [flagOf, Prod.mk.injEq] at e
  obtain ⟨e0, e1, e2⟩ := e
  exact RelIso.ext fun v => by rw [congrFun (eq_ext g) v, congrFun (eq_ext h) v, e0, e1, e2]

theorem exists_flagOf (p : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList) :
    ∃ g, flagOf g = p := ⟨mkAut _ _ _ (mem_triList p hp), flagOf_mkAut p _⟩

/-- The antipodal flag. -/
def flι (p : Fin 12 × Fin 12 × Fin 12) : Fin 12 × Fin 12 × Fin 12 :=
  (anti p.1, anti p.2.1, anti p.2.2)

theorem flagOf_mul_anti (g : Aut) : flagOf (g * antiAut) = flι (flagOf g) := by
  simp only [flagOf, flι, RelIso.mul_apply]
  exact Prod.ext (map_anti g 0) (Prod.ext (map_anti g 1) (map_anti g 2))

/-- Every numbering of a flag is even: compatible with the canonical orientation, which is
the class of the even numberings for this labelling of `T`. -/
theorem numb_even (p : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList) :
    ∃ σ ∈ alternatingGroup (Fin 5), ⇑σ = numb p := by
  obtain ⟨g, rfl⟩ := exists_flagOf p hp
  exact ⟨permT g * w0, mul_mem (permT_mem_alternating g)
    (by rw [Equiv.Perm.mem_alternatingGroup, w0, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; rfl),
    (numb_flagOf g).symm⟩

/-- Every even numbering is the numbering of a flag. -/
theorem numb_surjective (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ p ∈ triList, numb p = ⇑σ := by
  have hw : w0 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, w0, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]; rfl
  obtain ⟨g, hg⟩ := permT_surjective (σ * w0⁻¹) (mul_mem hσ (inv_mem hw))
  exact ⟨flagOf g, flagOf_mem g, by rw [numb_flagOf, hg, inv_mul_cancel_right]⟩

/-- Two flags have the same numbering if and only if they are equal or antipodal: the `60`
flags of `Π/ι` are the `60` even numberings of `T` (page 30). -/
theorem numb_eq_iff (p q : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList) (hq : q ∈ triList) :
    numb p = numb q ↔ q = p ∨ q = flι p := by
  obtain ⟨g, rfl⟩ := exists_flagOf p hp
  obtain ⟨h, rfl⟩ := exists_flagOf q hq
  rw [numb_flagOf, numb_flagOf, DFunLike.coe_fn_eq, mul_left_inj, ← flagOf_mul_anti,
    flagOf_injective.eq_iff, flagOf_injective.eq_iff]
  constructor
  · intro e
    have : permT (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    rcases (permT_eq_one_iff _).1 this with k | k
    · left; rw [inv_mul_eq_one] at k; exact k.symm
    · right; rw [inv_mul_eq_iff_eq_mul] at k; exact k
  · rintro (rfl | rfl)
    · rfl
    · rw [map_mul, permT_antiAut, mul_one]

/-! ### The involutions (pages 31–32) -/

/-- The flag involutions of the icosahedron: change the vertex, the edge, the face. -/
def fl0 (p : Fin 12 × Fin 12 × Fin 12) : Fin 12 × Fin 12 × Fin 12 := (p.2.1, p.1, p.2.2)
def fl1 (p : Fin 12 × Fin 12 × Fin 12) : Fin 12 × Fin 12 × Fin 12 := (p.1, p.2.2, p.2.1)
def fl2 (p : Fin 12 × Fin 12 × Fin 12) : Fin 12 × Fin 12 × Fin 12 :=
  (p.1, p.2.1, other p.1 p.2.1 p.2.2)

/-- Page 31: `σ₀ (a₁, …, a₅) = (a₁, a₄, a₅, a₂, a₃)`, as a permutation of the places. -/
def τ0 : Equiv.Perm (Fin 5) := Equiv.swap 1 3 * Equiv.swap 2 4
/-- `σ₁` as the dictionary of page 30 gives it: `(a₅, a₄, a₃, a₂, a₁)`. -/
def τ1 : Equiv.Perm (Fin 5) := Equiv.swap 0 4 * Equiv.swap 1 3
/-- Page 31: `σ₂ (a₁, …, a₅) = (a₁, a₅, a₄, a₃, a₂)`. -/
def τ2 : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 2 3
/-- `σ₁` as page 31 writes it: `(a₂, a₁, a₅, a₄, a₃)`. -/
def τ1' : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 4

/-- The four permutations of places, as the pages write them. -/
theorem tau_values :
    (⇑τ0 = ![0, 3, 4, 1, 2]) ∧ (⇑τ1 = ![4, 3, 2, 1, 0]) ∧ (⇑τ2 = ![0, 4, 3, 2, 1]) ∧
    (⇑τ1' = ![1, 0, 4, 3, 2]) := by decide +kernel

theorem s_tri : Tri 1 0 2 ∧ Tri 0 2 1 ∧ Tri 0 1 5 := by decide

theorem permT_s0 : permT (mkAut 1 0 2 s_tri.1) * w0 = w0 * τ0 := by decide +kernel
theorem permT_s1 : permT (mkAut 0 2 1 s_tri.2.1) * w0 = w0 * τ1 := by decide +kernel
theorem permT_s2 : permT (mkAut 0 1 5 s_tri.2.2) * w0 = w0 * τ2 := by decide +kernel

theorem other_zero : other 0 1 2 = 5 := by decide

/-- Pages 31–32: the three flag involutions act on numberings by the double transpositions of
places `τ0`, `τ1`, `τ2`, that is `σᵢ(a) = a ∘ τᵢ`. -/
theorem numb_sigma (p : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList) :
    numb (fl0 p) = numb p ∘ ⇑τ0 ∧ numb (fl1 p) = numb p ∘ ⇑τ1 ∧
      numb (fl2 p) = numb p ∘ ⇑τ2 := by
  obtain ⟨g, rfl⟩ := exists_flagOf p hp
  have f0 : fl0 (flagOf g) = flagOf (g * mkAut 1 0 2 s_tri.1) := rfl
  have f1 : fl1 (flagOf g) = flagOf (g * mkAut 0 2 1 s_tri.2.1) := rfl
  have f2 : fl2 (flagOf g) = flagOf (g * mkAut 0 1 5 s_tri.2.2) := by
    simp only [fl2, flagOf, RelIso.mul_apply]
    rw [← map_other g (by decide : Tri 0 1 2), other_zero]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [f0, numb_flagOf, numb_flagOf, map_mul, mul_assoc, permT_s0, ← mul_assoc]; rfl
  · rw [f1, numb_flagOf, numb_flagOf, map_mul, mul_assoc, permT_s1, ← mul_assoc]; rfl
  · rw [f2, numb_flagOf, numb_flagOf, map_mul, mul_assoc, permT_s2, ← mul_assoc]; rfl

theorem fl_mem (p : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList) :
    fl0 p ∈ triList ∧ fl1 p ∈ triList ∧ fl2 p ∈ triList := by
  obtain ⟨g, rfl⟩ := exists_flagOf p hp
  have f2 : fl2 (flagOf g) = flagOf (g * mkAut 0 1 5 s_tri.2.2) := by
    simp only [fl2, flagOf, RelIso.mul_apply]
    rw [← map_other g (by decide : Tri 0 1 2), other_zero]; rfl
  exact ⟨flagOf_mem (g * mkAut 1 0 2 s_tri.1), flagOf_mem (g * mkAut 0 2 1 s_tri.2.1),
    f2 ▸ flagOf_mem _⟩

/-- The page's `σ₁` is the conjugate of the dictionary's by `σ₂`, which commutes with `σ₀`. -/
theorem tau1'_eq : τ1' = τ2 * τ1 * τ2 ∧ τ0 * τ2 = τ2 * τ0 ∧ τ2 * τ2 = 1 := by decide +kernel

/-- The page's triple `(τ0, τ1', τ2)` is the action of the involutions of `Π` on the
numbering `p ↦ numb (fl2 p)`: the two triples give isomorphic `Γ̂`-sets. -/
theorem numb_sigma_page (p : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList) :
    numb (fl2 (fl0 p)) = numb (fl2 p) ∘ ⇑τ0 ∧ numb (fl2 (fl1 p)) = numb (fl2 p) ∘ ⇑τ1' ∧
      numb (fl2 (fl2 p)) = numb (fl2 p) ∘ ⇑τ2 := by
  obtain ⟨m0, m1, m2⟩ := fl_mem p hp
  obtain ⟨h0, h1, h2⟩ := numb_sigma p hp
  obtain ⟨e1, e2, e3⟩ := tau1'_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [(numb_sigma _ m0).2.2, h0, h2, Function.comp_assoc,
      Function.comp_assoc, ← Equiv.Perm.coe_mul, ← Equiv.Perm.coe_mul, e2]
  · rw [(numb_sigma _ m1).2.2, h1, h2, Function.comp_assoc,
      Function.comp_assoc, ← Equiv.Perm.coe_mul, ← Equiv.Perm.coe_mul, e1,
      show τ2 * (τ2 * τ1 * τ2) = τ1 * τ2 by rw [← mul_assoc, ← mul_assoc, e3, one_mul]]
  · rw [(numb_sigma _ m2).2.2, h2]

/-- Page 32, composing right to left on numberings: with the page's `σ₁`, `ρ_f = σ₁σ₀`,
`ρ_s = σ₂σ₁` and `σ₀σ₂` have the values written there and orders `3`, `5`, `2`; the page's
label « `σ₀σ₁` » for the third has the value of `σ₀σ₂`, and `σ₀σ₁` is of order `3`. -/
theorem page32 :
    (⇑(τ0 * τ1') = ![3, 0, 2, 1, 4]) ∧ (⇑(τ1' * τ2) = ![1, 2, 3, 4, 0]) ∧
    (⇑(τ2 * τ0) = ![0, 2, 1, 4, 3]) ∧
    ((τ0 * τ1') ^ 3 = 1 ∧ τ0 * τ1' ≠ 1) ∧ ((τ1' * τ2) ^ 5 = 1 ∧ τ1' * τ2 ≠ 1) ∧
    ((τ2 * τ0) ^ 2 = 1 ∧ τ2 * τ0 ≠ 1) ∧ ((τ1' * τ0) ^ 3 = 1 ∧ τ1' * τ0 ≠ 1) := by
  decide +kernel

/-! ### Vertices, edges, faces (pages 26–29, 31) -/

/-- `i, j` are adjacent in the pentagon traced by the numbering `a`. -/
def CycAdj (a : Fin 5 → Fin 5) (i j : Fin 5) : Prop :=
  ∃ k : Fin 5, (a k = i ∧ a (k + 1) = j) ∨ (a k = j ∧ a (k + 1) = i)

instance (a : Fin 5 → Fin 5) (i j : Fin 5) : Decidable (CycAdj a i j) := by
  unfold CycAdj; infer_instance

/-- The two numberings trace the same pentagon structure. -/
def SamePent (a b : Fin 5 → Fin 5) : Prop := ∀ i j, CycAdj a i j ↔ CycAdj b i j

instance (a b : Fin 5 → Fin 5) : Decidable (SamePent a b) := by unfold SamePent; infer_instance

/-- Same partition of type `(2, 2, 1)`, `{a₁} ⊔ {a₂, a₃} ⊔ {a₄, a₅}`. -/
def SamePart (a b : Fin 5 → Fin 5) : Prop :=
  a 0 = b 0 ∧ ((a 1 = b 1 ∧ a 2 = b 2 ∨ a 1 = b 2 ∧ a 2 = b 1) ∨
    (a 1 = b 3 ∧ a 2 = b 4 ∨ a 1 = b 4 ∧ a 2 = b 3))

instance (a b : Fin 5 → Fin 5) : Decidable (SamePart a b) := by unfold SamePart; infer_instance

/-- The three-element set `{a₁, a₃, a₅}`. -/
def faceSet (a : Fin 5 → Fin 5) : Finset (Fin 5) := {a 0, a 2, a 4}

/-- The face of a flag, as a set of vertices. -/
def faceOf (p : Fin 12 × Fin 12 × Fin 12) : Finset (Fin 12) := {p.1, p.2.1, p.2.2}

/-- Same face of `Π/ι`: the same face of `Π`, or antipodal faces. -/
def SameFace (p q : Fin 12 × Fin 12 × Fin 12) : Prop :=
  faceOf q = faceOf p ∨ faceOf q = faceOf (flι p)

instance (p q : Fin 12 × Fin 12 × Fin 12) : Decidable (SameFace p q) := by
  unfold SameFace; infer_instance

theorem base_dictionary : ∀ q ∈ triList,
    ((q.1 = 0 ∨ q.1 = anti 0) ↔ SamePent (numb (0, 1, 2)) (numb q)) ∧
    (SameDir (q.1, q.2.1) (0, 1) ↔ SamePart (numb (0, 1, 2)) (numb q)) ∧
    (SameFace (0, 1, 2) q ↔ faceSet (numb (0, 1, 2)) = faceSet (numb q)) := by
  decide +kernel

theorem cycAdj_map (σ : Equiv.Perm (Fin 5)) (a : Fin 5 → Fin 5) (i j : Fin 5) :
    CycAdj (⇑σ ∘ a) (σ i) (σ j) ↔ CycAdj a i j := by
  simp [CycAdj, σ.injective.eq_iff]

theorem samePent_map (σ : Equiv.Perm (Fin 5)) (a b : Fin 5 → Fin 5) :
    SamePent (⇑σ ∘ a) (⇑σ ∘ b) ↔ SamePent a b := by
  constructor
  · intro h i j
    rw [← cycAdj_map σ a, ← cycAdj_map σ b]; exact h _ _
  · intro h i j
    have e1 := cycAdj_map σ a (σ.symm i) (σ.symm j)
    have e2 := cycAdj_map σ b (σ.symm i) (σ.symm j)
    simp only [Equiv.apply_symm_apply] at e1 e2
    rw [e1, e2]; exact h _ _

theorem samePart_map (σ : Equiv.Perm (Fin 5)) (a b : Fin 5 → Fin 5) :
    SamePart (⇑σ ∘ a) (⇑σ ∘ b) ↔ SamePart a b := by
  simp [SamePart, σ.injective.eq_iff]

theorem faceSet_map (σ : Equiv.Perm (Fin 5)) (a : Fin 5 → Fin 5) :
    faceSet (⇑σ ∘ a) = (faceSet a).image σ := by
  simp [faceSet, Finset.image_insert, Finset.image_singleton]

theorem faceOf_mul (g k : Aut) : faceOf (flagOf (g * k)) = (faceOf (flagOf k)).image g := by
  simp [faceOf, flagOf, Finset.image_insert, Finset.image_singleton]

theorem flι_flagOf (g : Aut) : flι (flagOf g) = flagOf (g * antiAut) :=
  (flagOf_mul_anti g).symm

theorem numb_mul (g k : Aut) : numb (flagOf (g * k)) = ⇑(permT g) ∘ numb (flagOf k) := by
  rw [numb_flagOf, numb_flagOf, map_mul, mul_assoc]; rfl

/-- Pages 26–29 and 31: two flags have the same vertex in `Π/ι` if and only if their
numberings trace the same pentagon on `T`; the same edge if and only if they give the same
partition of type `(2, 2, 1)`; the same face if and only if they give the same three-element
set. -/
theorem incidence_dictionary (p q : Fin 12 × Fin 12 × Fin 12) (hp : p ∈ triList)
    (hq : q ∈ triList) :
    ((q.1 = p.1 ∨ q.1 = anti p.1) ↔ SamePent (numb p) (numb q)) ∧
    (SameDir (q.1, q.2.1) (p.1, p.2.1) ↔ SamePart (numb p) (numb q)) ∧
    (SameFace p q ↔ faceSet (numb p) = faceSet (numb q)) := by
  obtain ⟨g, rfl⟩ := exists_flagOf p hp
  obtain ⟨h, rfl⟩ := exists_flagOf q hq
  set k := g⁻¹ * h
  have hk : h = g * k := by simp [k]
  obtain ⟨b1, b2, b3⟩ := base_dictionary (flagOf k) (flagOf_mem k)
  have e0 : flagOf g = flagOf (g * 1) := by rw [mul_one]
  have nb : numb (flagOf g) = ⇑(permT g) ∘ numb (0, 1, 2) := by
    rw [e0, numb_mul]; rfl
  rw [hk, numb_mul, nb]
  refine ⟨?_, ?_, ?_⟩
  · rw [samePent_map, ← b1]
    simp only [flagOf, RelIso.mul_apply, ← map_anti, g.injective.eq_iff]
  · rw [samePart_map, ← b2]
    exact ⟨fun hd => by simpa [gP, flagOf] using map_sameDir g⁻¹ hd,
      fun hd => by simpa [gP, flagOf] using map_sameDir g hd⟩
  · rw [faceSet_map, faceSet_map, (Finset.image_injective (permT g).injective).eq_iff, ← b3]
    have f1 : faceOf (flagOf g) = (faceOf (0, 1, 2)).image g := by rw [e0, faceOf_mul]; rfl
    have f2 : faceOf (flι (flagOf g)) = (faceOf (flι (0, 1, 2))).image g := by
      rw [flι_flagOf, faceOf_mul]; rfl
    simp only [SameFace]
    rw [faceOf_mul, f1, f2, (Finset.image_injective g.injective).eq_iff,
      (Finset.image_injective g.injective).eq_iff]

/-- The ten rotations and reflections of the pentagon `0 – 1 – 2 – 3 – 4`, as permutations
of the places. -/
def dihedral : List (Equiv.Perm (Fin 5)) :=
  [1, finRotate 5, finRotate 5 ^ 2, finRotate 5 ^ 3, finRotate 5 ^ 4,
    w0, finRotate 5 * w0, finRotate 5 ^ 2 * w0, finRotate 5 ^ 3 * w0, finRotate 5 ^ 4 * w0]

/-- The numberings tracing the standard pentagon are the ten numberings of the dihedral
group. -/
theorem samePent_id : ∀ a0 a1 a2 a3 a4 : Fin 5, SamePent id ![a0, a1, a2, a3, a4] →
    ∃ d ∈ dihedral, ⇑d = ![a0, a1, a2, a3, a4] := by decide +kernel

/-- Page 21, « type `n ≡ 1 (4)` »: the symmetries of a pentagon are even permutations. -/
theorem dihedral_even : ∀ d ∈ dihedral, Equiv.Perm.sign d = 1 := by decide +kernel

theorem samePent_sign (σ τ : Equiv.Perm (Fin 5)) (h : SamePent ⇑σ ⇑τ) :
    Equiv.Perm.sign σ = Equiv.Perm.sign τ := by
  have h' : SamePent id ⇑(σ⁻¹ * τ) := by
    rw [← samePent_map σ⁻¹] at h
    simpa [Equiv.Perm.coe_mul] using h
  have e : ⇑(σ⁻¹ * τ) = ![(σ⁻¹ * τ) 0, (σ⁻¹ * τ) 1, (σ⁻¹ * τ) 2, (σ⁻¹ * τ) 3,
      (σ⁻¹ * τ) 4] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h'
  obtain ⟨d, hd, hd'⟩ := samePent_id _ _ _ _ _ h'
  have hdσ : d = σ⁻¹ * τ := Equiv.ext (fun i => by rw [hd', ← e])
  have hs := dihedral_even d hd
  rw [hdσ, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv] at hs
  calc Equiv.Perm.sign σ = Equiv.Perm.sign σ * (Equiv.Perm.sign σ * Equiv.Perm.sign τ) := by
        rw [hs, mul_one]
    _ = Equiv.Perm.sign τ := by rw [← mul_assoc, Int.units_mul_self, one_mul]

/-- Pages 26–27: a numbering traces the pentagon of a vertex of `Π/ι` if and only if it is
even. With the twelve pentagon structures on `T` and ten numberings for each, the vertices are
the six pentagons compatible with the orientation. -/
theorem vertex_pentagons (σ : Equiv.Perm (Fin 5)) :
    (∃ p ∈ triList, SamePent (numb p) ⇑σ) ↔ σ ∈ alternatingGroup (Fin 5) := by
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨τ, hτ, e⟩ := numb_even p hp
    rw [← e] at h
    rw [Equiv.Perm.mem_alternatingGroup] at hτ ⊢
    rw [← samePent_sign τ σ h, hτ]
  · intro hσ
    obtain ⟨p, hp, e⟩ := numb_surjective σ hσ
    exact ⟨p, hp, by rw [e]; exact fun _ _ => Iff.rfl⟩

/-- The pentagon traced by a numbering, as its set of five sides. -/
def pentSet (a : Fin 5 → Fin 5) : Finset (Finset (Fin 5)) :=
  Finset.univ.image fun k => {a k, a (k + 1)}

/-- The partition `{a₁} ⊔ {a₂, a₃} ⊔ {a₄, a₅}`. -/
def partSet (a : Fin 5 → Fin 5) : Finset (Finset (Fin 5)) := {{a 0}, {a 1, a 2}, {a 3, a 4}}

/-- The counts of pages 26–27 and 31: `6` pentagons, `15` partitions of type `(2, 2, 1)`
(all of them: there are `5 · 3`), and all `10` three-element subsets. -/
theorem counts :
    (triList.map (pentSet ∘ numb)).toFinset.card = 6 ∧
    (triList.map (partSet ∘ numb)).toFinset.card = 15 ∧
    (triList.map (faceSet ∘ numb)).toFinset = Finset.powersetCard 3 Finset.univ := by
  decide +kernel

end Grothendieck.Folder86
