module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder115

open CategoryTheory Opposite Limits

universe u

variable {A : Type u} [SmallCategory A] {C : Type u} [SmallCategory C]

/-- The left transform `ˢK(L)(c) = Hom(L, K(-, c))` of a kernel `K`, contravariant in `L`. -/
abbrev kernelS (K : Aᵒᵖ ⥤ C ⥤ Type u) : (Aᵒᵖ ⥤ Type u)ᵒᵖ ⥤ C ⥤ Type u :=
  (K.flip ⋙ yoneda).flip

/-- `𝒪 : Â → (A^∨)^op`, the kernel transform at `K = Hom_A`. -/
abbrev isbellO : (Aᵒᵖ ⥤ Type u) ⥤ (A ⥤ Type u)ᵒᵖ := (kernelS (coyoneda (C := A))).rightOp

/-- `𝒪` sends colimits of presheaves to colimits of `(A^∨)^op`, i.e. limits of
copresheaves; dually `Spec` preserves limits. -/
theorem isbellO_preservesColimits :
    PreservesColimitsOfSize.{u, u} (isbellO : (Aᵒᵖ ⥤ Type u) ⥤ _) := by
  sorry

universe v

end Grothendieck.Folder115
