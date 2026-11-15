module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/subalgebra-isUnit-of-isIntegral`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/subalgebra-isUnit-of-isIntegral`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/RingTheory/Artinian/Algebra.lean` -/

namespace IsArtinianRing
variable {R A : Type*}
variable [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
open nonZeroDivisors
theorem isUnit_of_isIntegral_of_isUnit {B : Subalgebra R A} {a : B} (hi : IsIntegral R (a : A))
    (ha : IsUnit (a : A)) : IsUnit a :=
  isUnit_of_isIntegral_of_nonZeroDivisor
    ((isIntegral_algHom_iff B.val Subtype.val_injective).mp hi)
    (comap_nonZeroDivisors_le_of_injective (f := B.val) Subtype.val_injective
      ha.mem_nonZeroDivisors)

/-- Over an Artinian ring `R`, an `R`-subalgebra `B` of `A` contains the inverse of every unit
of `A` which lies in `B` and is integral over `R`. For instance, when `R = K` is a field, a
`K`-subalgebra of `Module.End K V` with `V` finite-dimensional is closed under taking inverses. -/
theorem inv_mem_of_isIntegral {B : Subalgebra R A} {u : Aˣ} (hi : IsIntegral R (u : A))
    (hu : (u : A) ∈ B) : ((u⁻¹ : Aˣ) : A) ∈ B := by
  obtain ⟨v, hv⟩ := isUnit_of_isIntegral_of_isUnit (a := (⟨u, hu⟩ : B)) hi u.isUnit
  rw [← (Units.ext (congrArg Subtype.val hv) : Units.map (B.val : B →* A) v = u)]
  exact (↑v⁻¹ : B).2

end IsArtinianRing
