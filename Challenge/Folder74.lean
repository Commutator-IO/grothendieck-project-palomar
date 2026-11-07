module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Abel

@[expose] public section

namespace Grothendieck.Folder74

noncomputable section

open Function

section Axioms

variable {V : Type*} (G : SimpleGraph V)

/-- Axiom 1: every edge lies in a unique triangle. -/
def Axiom1 : Prop := ∀ x y, G.Adj x y → ∃! z, G.Adj x z ∧ G.Adj y z

end Axioms

universe u

/-- The points of `∐ Ẽ_α`. -/
abbrev Pt (X : Fin 3 → Type u) : Type u := Σ α, X α

/-- The data of the Scholie of page 96 on three sets `Ẽ_α = X α`: fixed-point-free
involutions `σ_α`, and a set `T ⊆ ∏ Ẽ_α` of triples (the upper triangles). -/
structure Scholie (X : Fin 3 → Type u) where
  σ : ∀ α, X α → X α
  σσ : ∀ α s, σ α (σ α s) = s
  σne : ∀ α s, σ α s ≠ s
  T : Set (∀ α, X α)

namespace Scholie

variable {X : Fin 3 → Type u} (D : Scholie X)

/-- The involution `σ` on `∐ Ẽ_α`. -/
def sg (p : Pt X) : Pt X := ⟨p.1, D.σ p.1 p.2⟩

/-- Two points of distinct `Ẽ`'s are linked when a triple of `T` contains both. -/
def Lk (p q : Pt X) : Prop := p.1 ≠ q.1 ∧ ∃ τ ∈ D.T, τ p.1 = p.2 ∧ τ q.1 = q.2

/-- Condition (*): the projections of `T` on two factors are injective. -/
def Star : Prop :=
  ∀ τ ∈ D.T, ∀ ρ ∈ D.T, ∀ α β, α ≠ β → τ α = ρ α → τ β = ρ β → τ = ρ

/-- Condition `β_Γ̃` (page 101, with Prop. 5 of page 98): of the two points of an
orbit of `σ_α`, exactly one is linked to a given point of `Ẽ_β`, `β ≠ α`. -/
def Beta : Prop := ∀ p q : Pt X, p.1 ≠ q.1 → (D.Lk (D.sg p) q ↔ ¬ D.Lk p q)

/-- Condition (***) = (Ka) of the margin of page 96, in the form used here: three
triples `τ, ρ₁, ρ₂ ∈ T` through the pairs `(s_α, s_β)`, `(s_α, s_γ)`, `(s_β, s_γ)`
of one family `(s_α, s_β, s_γ)` coincide. -/
def Ka : Prop :=
  ∀ α β γ : Fin 3, α ≠ β → α ≠ γ → β ≠ γ → ∀ τ ∈ D.T, ∀ ρ₁ ∈ D.T, ∀ ρ₂ ∈ D.T,
    τ α = ρ₁ α → τ β = ρ₂ β → ρ₁ γ = ρ₂ γ → τ = ρ₁

theorem sg_sg (p : Pt X) : D.sg (D.sg p) = p := by
  obtain ⟨α, s⟩ := p; simp [sg, D.σσ]

theorem sg_ne (p : Pt X) : D.sg p ≠ p := by
  obtain ⟨α, s⟩ := p
  intro h
  simp only [sg, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact D.σne α s h

theorem Lk_symm {p q : Pt X} (h : D.Lk p q) : D.Lk q p := by
  obtain ⟨hne, τ, hτ, h1, h2⟩ := h
  exact ⟨Ne.symm hne, τ, hτ, h2, h1⟩

theorem Lk_irrefl (p : Pt X) : ¬ D.Lk p p := fun h => h.1 rfl

/-- Adjacency on `t₀ ⊔ ∐ Ẽ_α` (Scholie, 2°) α)–δ)). -/
def Adj : Fin 3 ⊕ Pt X → Fin 3 ⊕ Pt X → Prop
  | .inl α, .inl β => α ≠ β
  | .inl α, .inr p => p.1 = α
  | .inr p, .inl α => p.1 = α
  | .inr p, .inr q => q = D.sg p ∨ D.Lk p q

/-- The graph of the Scholie, on `t₀ ⊔ ∐ Ẽ_α`. -/
def graph : SimpleGraph (Fin 3 ⊕ Pt X) where
  Adj := D.Adj
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [Adj] at h ⊢
    · exact Ne.symm h
    · exact h
    · exact h
    · rcases h with rfl | h
      · exact Or.inl (D.sg_sg _).symm
      · exact Or.inr (D.Lk_symm h)⟩
  loopless := ⟨fun a h => by
    cases a <;> simp only [Adj] at h
    · exact h rfl
    · rcases h with h | h
      · exact D.sg_ne _ h.symm
      · exact D.Lk_irrefl _ h⟩

/-- Under (*) and `β_Γ̃`, the graph satisfies axiom 1 if and only if (Ka) holds;
it then satisfies axiom 2. -/
theorem axiom1_iff_ka (hS : D.Star) (hB : D.Beta) : Axiom1 D.graph ↔ D.Ka := by
  sorry

end Scholie

end

end Grothendieck.Folder74
