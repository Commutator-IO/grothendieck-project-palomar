module

public import Mathlib
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Relation

@[expose] public section


/-!
# Folder 152, the dictionary of pages 7 and 9 (partial)

**This file is partial.** Issue #26 names, for this folder, the
correspondence between embeddings of a graph in an oriented surface and
rotation systems (the reading's Proposition of page 4). mathlib has no
topological surfaces, no embeddings of CW-complexes and no classification of
surfaces, so that Proposition is out of reach without building the theory;
it is not formalised. Nor is the boxed *Critère* of page 9 (a circularised
graph is a non-trivial tree iff its contour is one polygon whose gluing
involution is non-crossing): its proof in the reading goes through Euler's
formula and the genus of the glued surface, i.e. the theory of genus for
combinatorial maps, which mathlib also lacks.

What is formalised is the combinatorial half the reading states in closed
form, `transcripts/152/152.modern.tex`, pages 7 and 9:

> en identifiant `A(C)` à `Ā` par `rd`,
> `σ_C = σ_Γ`, `ρ_C = ρ_Γ σ_Γ`, `ρ_Γ = ρ_C σ_C`,
> les cycles de `ρ_C` étant les polygones du contour, c'est-à-dire les faces,
> et les orbites de `ρ_C σ_C` les sommets.
>
> **Équivalence.** La catégorie des graphes combinatoires circularisés sans
> sommet isolé est équivalente à celle des contours orientés `(A(C), ρ_C)`
> munis d'une involution sans point fixe `σ_C` de `A(C)`. Dans les deux sens,
> l'ensemble sous-jacent est le même, et l'on passe d'un couple de permutations
> à l'autre par les formules ci-dessus.

and, from the proof of the *Critère*: « `Γ` est connexe puisque `ρ_C` n'a
qu'un cycle ».

A circularised graph without isolated vertices is encoded, as the reading
does, by its set of arcs `Ā` with the reversal `σ_Γ` (a fixed-point-free
involution) and the rotation `ρ_Γ` (a permutation whose orbits are the
vertices, `S ≃ Ā/ρ_Γ`). The equivalence is proved on objects
(`dictionnaire`), with the reading's formulas as definitional equalities and
both round trips; morphisms are not examined, as the reading does not examine
them either.

What the formalisation found. The reading's convention is consistent: the
three formulas hold together because `σ_Γ² = 1`, and nothing else is needed.
It also confirms the reading's footnote that the page's own head line
« `σ_Γ = σ_C`, `ρ_Γ = ρ_C` » cannot be combined with the table: together with
`ρ_C = ρ_Γ σ_Γ` it would force `σ_Γ = 1`, impossible for a fixed-point-free
involution on a non-empty set of arcs (`tete_page9_incompatible`). The
connectivity step holds as stated (`connexe_of_une_face`).
-/

namespace Grothendieck.Folder152

open Equiv

variable {D : Type*}

/-- A fixed-point-free involution of `D`. -/
structure InvolutionSansPointFixe (D : Type*) where
  /-- The involution. -/
  σ : Perm D
  invol : ∀ a, σ (σ a) = a
  sansPointFixe : ∀ a, σ a ≠ a

theorem InvolutionSansPointFixe.mul_self (s : InvolutionSansPointFixe D) :
    s.σ * s.σ = 1 :=
  Equiv.ext s.invol

/-- A combinatorial circularised graph without isolated vertex, on the set of
arcs `D = Ā`: the reversal `σ_Γ` and the rotation `ρ_Γ` (next arc around the
origin). Its vertices are the orbits of `ρ_Γ`. -/
structure GrapheCircularise (D : Type*) where
  /-- The reversal of arcs `σ_Γ`. -/
  σ : InvolutionSansPointFixe D
  /-- The rotation `ρ_Γ`. -/
  ρ : Perm D

/-- An oriented contour `(A(C), ρ_C)` with a fixed-point-free gluing involution
`σ_C`; its polygons (faces) are the cycles of `ρ_C`. -/
structure Contour (D : Type*) where
  /-- "Next edge" on the oriented contour, `ρ_C`. -/
  ρC : Perm D
  /-- The gluing involution `σ_C`. -/
  σC : InvolutionSansPointFixe D

/-- From the graph to its contour: `σ_C = σ_Γ`, `ρ_C = ρ_Γ σ_Γ`. -/
def GrapheCircularise.contour (Γ : GrapheCircularise D) : Contour D :=
  ⟨Γ.ρ * Γ.σ.σ, Γ.σ⟩

/-- From the contour back to the graph: `σ_Γ = σ_C`, `ρ_Γ = ρ_C σ_C`. -/
def Contour.graphe (C : Contour D) : GrapheCircularise D :=
  ⟨C.σC, C.ρC * C.σC.σ⟩

/-- **Équivalence** (on objects). Circularised graphs without isolated vertex
on `Ā` and contours with a fixed-point-free involution on the same set
correspond, by `σ_C = σ_Γ`, `ρ_C = ρ_Γ σ_Γ` and `ρ_Γ = ρ_C σ_C`. -/
def dictionnaire : GrapheCircularise D ≃ Contour D where
  toFun := GrapheCircularise.contour
  invFun := Contour.graphe
  left_inv Γ := by
    obtain ⟨σ, ρ⟩ := Γ
    simp only [GrapheCircularise.contour, Contour.graphe, mul_assoc, σ.mul_self, mul_one]
  right_inv C := by
    obtain ⟨ρC, σ⟩ := C
    simp only [GrapheCircularise.contour, Contour.graphe, mul_assoc, σ.mul_self, mul_one]

/-- The three formulas of the dictionary, all at once: `σ_C = σ_Γ`,
`ρ_C = ρ_Γ σ_Γ`, `ρ_Γ = ρ_C σ_C`. -/
theorem formules (Γ : GrapheCircularise D) :
    (dictionnaire Γ).σC = Γ.σ ∧ (dictionnaire Γ).ρC = Γ.ρ * Γ.σ.σ ∧
      Γ.ρ = (dictionnaire Γ).ρC * (dictionnaire Γ).σC.σ := by
  refine ⟨rfl, rfl, ?_⟩
  change Γ.ρ = Γ.ρ * Γ.σ.σ * Γ.σ.σ
  rw [mul_assoc, Γ.σ.mul_self, mul_one]

/-- The vertices of `Γ` (orbits of `ρ_Γ`) are the orbits of `ρ_C σ_C`. -/
theorem sommets (Γ : GrapheCircularise D) (a b : D) :
    ((dictionnaire Γ).ρC * (dictionnaire Γ).σC.σ).SameCycle a b ↔ Γ.ρ.SameCycle a b := by
  rw [← (formules Γ).2.2]

/-- The page's head line « `σ_Γ = σ_C`, `ρ_Γ = ρ_C` » is incompatible with
`ρ_C = ρ_Γ σ_Γ` as soon as there is an arc. -/
theorem tete_page9_incompatible (Γ : GrapheCircularise D) (a : D) :
    Γ.ρ ≠ Γ.ρ * Γ.σ.σ := by
  intro h
  have : Γ.σ.σ = 1 := by simpa using (congrArg (Γ.ρ⁻¹ * ·) h).symm
  exact Γ.σ.sansPointFixe a (by rw [this]; rfl)

/-- Connectedness of the graph: any two arcs are joined by a chain of moves
`x ↦ ρ_Γ x` and `x ↦ σ_Γ x` (taken in either direction). -/
def GrapheCircularise.Connexe (Γ : GrapheCircularise D) : Prop :=
  ∀ a b, Relation.EqvGen (fun x y => y = Γ.ρ x ∨ y = Γ.σ.σ x) a b

/-- « `Γ` est connexe puisque `ρ_C` n'a qu'un cycle »: if the contour has a
single polygon (`ρ_C` has one orbit), the graph is connected. -/
theorem connexe_of_une_face [Finite D] (Γ : GrapheCircularise D)
    (h : ∀ a b, (dictionnaire Γ).ρC.SameCycle a b) : Γ.Connexe := by
  intro a b
  obtain ⟨k, hk⟩ := (h a b).exists_nat_pow_eq
  subst hk
  induction k with
  | zero => exact Relation.EqvGen.refl _
  | succ k ih =>
    refine (ih.trans _ _ _ (.rel _ _ (Or.inr rfl))).trans _ _ _ (.rel _ _ (Or.inl ?_))
    rw [pow_succ']
    rfl

end Grothendieck.Folder152
