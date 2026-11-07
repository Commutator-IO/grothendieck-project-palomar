module

public import Mathlib

@[expose] public section

open Set Topology

namespace Grothendieck.Folder151

/-- The plane `X = X₂`. -/
abbrev P := ℝ × ℝ

/-- The closed stratum `X₁`, the horizontal axis. -/
def axis : Set P := {p | p.2 = 0}

/-- The closed stratum `X₀ = X₀* = {0}`. -/
def X0 : Set P := {0}

/-- The open stratum `X₁* = X₁ ∖ X₀`. -/
def X1s : Set P := axis \ X0

/-- The open stratum `X₂* = X₂ ∖ X₁`. -/
def X2s : Set P := axisᶜ

/-- Arbitrary choices of the closed tubes `𝒱̄_{0,1}` (of `X₀` in `X₁`) and `𝒱̄_{1,2}`
(of `X₁` in `X₂`), each containing its soul. -/
structure Tubes where
  V01bar : Set P
  V12bar : Set P
  V01bar_subset : V01bar ⊆ axis
  X0_subset : X0 ⊆ V01bar
  axis_subset : axis ⊆ V12bar

namespace Tubes

variable (T : Tubes)

/-- `𝒱_{0,1} = 𝒱̄_{0,1} ∖ R_{0,1}`, with `R_{0,1} = ∅`. -/
def V01 : Set P := T.V01bar \ ∅

/-- `𝒱*_{0,1} = 𝒱̄_{0,1} ∖ Ẋ₁`, with `Ẋ₁ = X₀`. -/
def V01s : Set P := T.V01bar \ X0

/-- `𝒱_{1,2} = 𝒱̄_{1,2} ∖ R_{1,2}`, with `R_{1,2} = X₀`. -/
def V12 : Set P := T.V12bar \ X0

/-- `𝒱*_{1,2} = 𝒱̄_{1,2} ∖ Ẋ₂`, with `Ẋ₂ = X₁`. -/
def V12s : Set P := T.V12bar \ axis

/-- The seven vertices of `Ĩ`: `X₀*, 𝒱_{0,1}, 𝒱*_{0,1}, X₁*, 𝒱_{1,2}, 𝒱*_{1,2}, X₂*`. -/
def piece : Fin 7 → Set P := ![X0, T.V01, T.V01s, X1s, T.V12, T.V12s, X2s]

/-- The colimit topology: the finest making the inclusions of the seven vertices continuous. -/
@[instance_reducible]
def colimTop : TopologicalSpace P :=
  ⨆ i, TopologicalSpace.coinduced (Subtype.val : T.piece i → P) inferInstance

/-- The colimit topology of `Ĩ` is not the topology of `ℝ²`: the gluing theorem of page 68,
read as a colimit in `Top`, fails for `ℝ² ⊃ ℝ × {0} ⊃ {0}`, whatever the tubes. -/
theorem colimTop_ne : T.colimTop ≠ (inferInstance : TopologicalSpace P) := by
  sorry

end Tubes

end Grothendieck.Folder151

namespace Grothendieck.Folder151

namespace DepthOne

variable {X : Type*} [TopologicalSpace X] (X₀ V : Set X)

/-- The four vertices of `Ĩ` for `X ⊃ X₀`: `X₀* = X₀`, `𝒱_{0,1} = 𝒱̄` (here `R_{0,1} = ∅`),
`𝒱*_{0,1} = 𝒱̄ ∖ X₀` (here `Ẋ₁ = X₀`) and `X₁* = X ∖ X₀`. -/
def piece : Fin 4 → Set X := ![X₀, V, V \ X₀, X₀ᶜ]

/-- The colimit topology: the finest making the inclusions of the four vertices continuous. -/
@[instance_reducible]
def colimTop : TopologicalSpace X :=
  ⨆ i, TopologicalSpace.coinduced (Subtype.val : piece X₀ V i → X) inferInstance

end DepthOne

end Grothendieck.Folder151
