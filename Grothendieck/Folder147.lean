module

public import Mathlib
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Rat.Init

@[expose] public section


/-!
# Folder 147, pages 62–64: the stratified class of `M₁,₁` over `ℤ`

The page computes the class of the moduli stack of elliptic curves over all of `ℤ` by cutting the
`j`-line `𝔸¹_ℤ` along the two sections `S₀` (`j = 1728`, automorphisms `ℤ/4`) and `S₁` (`j = 0`,
automorphisms `ℤ/6`), which meet only over `𝔽₂` and `𝔽₃`, where the automorphism groups have order
24 and 12. With `𝕃` the class of the affine line and `ζ_p` the class of `Spec 𝔽_p`, the strata give

  `[M₁,₁] = ½[U] + ¼[S'₀] + ⅙[S'₁] + (1/24) ζ₂ + (1/12) ζ₃`,
  `[U] = 𝕃 − 2 + ζ₂ + ζ₃`, `[S'ᵢ] = 1 − ζ₂ − ζ₃`,

and the page's formula (80) is `[M₁,₁] = ½(𝕃 − 1) − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`; adding the cusp, with
weight ½, gives `[M̄₁,₁] = ½ 𝕃 − 1/12 + ⅛ ζ₂ + ⅙ ζ₃`. The modernised reading says it redid the
computation (« il est juste »); this file checks the arithmetic, over any field of characteristic
zero, with `𝕃`, `ζ₂`, `ζ₃` as indeterminates. It checks the algebra of the strata,
not the geometry that produces them.
-/

namespace Grothendieck.Folder147

variable {K : Type*} [Field K] [CharZero K]

/-- Formula (80) of folder 147, page 63, from the stratification of the `j`-line. -/
theorem class_M11 (L z₂ z₃ : K) :
    (1 / 2) * (L - 2 + z₂ + z₃) + (1 / 4) * (1 - z₂ - z₃) + (1 / 6) * (1 - z₂ - z₃)
        + (1 / 24) * z₂ + (1 / 12) * z₃
      = (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  ring

/-- The compactified class: the cusp adds `½`. -/
theorem class_M11_bar (L z₂ z₃ : K) :
    ((1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃) + 1 / 2
      = (1 / 2) * L - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  ring

/-- Over `ℤ[1/6]` the correction terms vanish and (80) becomes (79). -/
theorem class_M11_away_from_6 (L : K) :
    (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * 0 + (1 / 6) * 0 = (1 / 2) * (L - 1) - 1 / 12 := by
  ring

end Grothendieck.Folder147
