module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Relation

@[expose] public section

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
  sorry

end Grothendieck.Folder152
