module

public import Mathlib.Tactic.Ring
public import Mathlib.Data.Rat.Init

@[expose] public section

namespace Grothendieck.Folder147

variable {K : Type*} [Field K] [CharZero K]

/-- Formula (80) of folder 147, page 63, from the stratification of the `j`-line. -/
theorem class_M11 (L z₂ z₃ : K) :
    (1 / 2) * (L - 2 + z₂ + z₃) + (1 / 4) * (1 - z₂ - z₃) + (1 / 6) * (1 - z₂ - z₃)
        + (1 / 24) * z₂ + (1 / 12) * z₃
      = (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  sorry

end Grothendieck.Folder147
