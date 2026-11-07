module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.GroupTheory.SpecificGroups.Alternating

@[expose] public section

namespace Grothendieck.Folder86

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

/-- `ρ₀` passes to directions. -/
theorem rho0_sameDir : ∀ p q, IsEdge p → SameDir p q → SameDir (rho0 p) (rho0 q) := by
  decide +kernel

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

/-- Page 25: `G → Alt_T` is onto. -/
theorem permT_surjective (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ g, permT g = σ := by
  sorry

end Grothendieck.Folder86
