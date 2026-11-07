module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder40

open Polynomial IsLocalRing

section PowerSeries

variable {k : Type*} [Field k]

/-- The cusp `S = k[[X]][T]/(T^n - X²)`. -/
abbrev Cusp (k : Type*) [Field k] (n : ℕ) := AdjoinRoot (X ^ n - C (PowerSeries.X ^ 2 : (PowerSeries k)))

theorem not_isDVR_cusp_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    ¬ ∃ _ : IsDomain (Cusp k n), IsDiscreteValuationRing (Cusp k n) := by
  sorry

end PowerSeries

end Grothendieck.Folder40
