module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder80Maps1

open Filter Topology Matrix

section SignVectors

variable {E : Type*}

/-- `Z` is a face of `X` (conformal order): `Z e ∈ {0, X e}` for all `e`. -/
def Conf (Z X : E → SignType) : Prop := ∀ e, Z e = 0 ∨ Z e = X e

/-- The closed cell of `ℝP²` of the cell `±X`: the nonzero covectors `Z ≤ ±X`. -/
def PCl (L : Set (E → SignType)) (X : E → SignType) : Set (E → SignType) :=
  {Z | Z ∈ L ∧ Z ≠ 0 ∧ (Conf Z X ∨ Conf Z (-X))}

/-- The « cas latticiel »: two closed cells meet in nothing or in a single closed cell. -/
def Lattice (L : Set (E → SignType)) : Prop :=
  ∀ X ∈ L, ∀ Y ∈ L, X ≠ 0 → Y ≠ 0 →
    PCl L X ∩ PCl L Y = ∅ ∨ ∃ W ∈ L, W ≠ 0 ∧ PCl L X ∩ PCl L Y = PCl L W

variable {L : Set (E → SignType)}

end SignVectors

section Lines

variable {ι : Type*} (ℓ : ι → Fin 3 → ℝ)

/-- The sign vector of a point. -/
noncomputable def sgn (p : Fin 3 → ℝ) : ι → SignType := fun i => SignType.sign (ℓ i ⬝ᵥ p)

/-- The covectors of the arrangement. -/
def cov : Set (ι → SignType) := Set.range (sgn ℓ)

/-- Two points that carry every line between them, neither on all the lines: the arrangement
is covered by two pencils (types `I_N`, `I_{p,q}`, `II′_{p,q}`). -/
def TwoPencil : Prop :=
  ∃ p q : Fin 3 → ℝ, sgn ℓ p ≠ 0 ∧ sgn ℓ q ≠ 0 ∧ ∀ i, ℓ i ⬝ᵥ p = 0 ∨ ℓ i ⬝ᵥ q = 0

variable {ℓ}

/-- **The lattice criterion for lines.** The arrangement is latticial iff no two points carry
every line between them. -/
theorem lattice_iff_not_twoPencil [Fintype ι] : Lattice (cov ℓ) ↔ ¬ TwoPencil ℓ := by
  sorry

end Lines

end Grothendieck.Folder80Maps1
