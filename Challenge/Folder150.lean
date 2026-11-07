module

public import Mathlib

@[expose] public section

open Set

namespace Grothendieck.Folder150

/-- The space `X = [0, 1]`. -/
def X : Set ℝ := Icc 0 1

/-- The closed part `Y = {0}`. -/
def Y : Set ℝ := {0}

/-- The conic neighbourhood `T = [0, 1/2]` of `Y`, for the action `(λ, t) ↦ λ t`. -/
def T : Set ℝ := Icc 0 (1 / 2)

/-- Its boundary `Ṫ = {1/2}`. -/
def Tdot : Set ℝ := {1 / 2}

/-- `X* = X ∖ T° = [1/2, 1]`. -/
def Xstar : Set ℝ := Icc (1 / 2) 1

/-- The cone `I · S = {λ s | λ ∈ [0, 1], s ∈ S}`. -/
def cone (S : Set ℝ) : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Icc 0 1 ×ˢ S)

/-- `C ⊂ T` is conic: `C = I · (C ∩ Ṫ) ∪ (C ∩ Y)` (page 15). -/
def IsConic (C : Set ℝ) : Prop := C ⊆ T ∧ C = cone (C ∩ Tdot) ∪ (C ∩ Y)

/-- `T` is compatible with the closed part `X₁ ⊂ X`: `X₁ ∩ T` is conic. -/
def IsCompatible (X₁ : Set ℝ) : Prop := IsClosed X₁ ∧ X₁ ⊆ X ∧ IsConic (X₁ ∩ T)

/-- `X₁` is compatible with the collar `E = [1/2, 3/4] ≃ Ṫ × [0, 1]`: `X₁ ∩ E = X₁₀ × [0, 1]`
with `X₁₀ = X₁ ∩ Ṫ`. -/
def IsCollarCompatible (X₁ : Set ℝ) : Prop :=
  X₁ ∩ Icc (1 / 2) (3 / 4) = (fun p : ℝ × ℝ => p.1 + p.2 / 4) '' ((X₁ ∩ Tdot) ×ˢ Icc 0 1)

/-- The edition's counterexample (reading, footnote to page 19): `X₁ = {0}` and `X₁ = ∅` are
both compatible with `T` and with the collar, and have the same trace on `X*` — the same
right-hand data `(X*, Ṫ, X₁*, Y, f)` — but `{0}` is nonempty and `∅` is not, so no
isomorphism of systems takes one to the other. -/
theorem compatible_not_determined :
    IsCompatible {0} ∧ IsCompatible ∅ ∧ IsCollarCompatible {0} ∧ IsCollarCompatible ∅ ∧
      ({0} : Set ℝ) ∩ Xstar = ∅ ∩ Xstar ∧ ({0} : Set ℝ).Nonempty := by
  sorry

end Grothendieck.Folder150
