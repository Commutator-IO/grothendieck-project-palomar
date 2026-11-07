module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/derivation-lie-mulLeft`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/derivation-lie-mulLeft`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/RingTheory/Derivation/Lie.lean` -/

namespace Derivation
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {D1 D2 : Derivation R A A} (a : A)
section LieStructures
theorem lie_mulLeft (D : Derivation R A A) :
    ⁅(D : Module.End R A), LinearMap.mulLeft R a⁆ = LinearMap.mulLeft R (D a) := by
  ext; simp [Ring.lie_def, leibniz, mul_comm]

/-- Conjugating a derivation by multiplication by a unit `u` subtracts multiplication by the
logarithmic derivative `u⁻¹ * D u`. -/
theorem mulLeft_mul_mul_mulLeft_inv (D : Derivation R A A) (u : Aˣ) :
    LinearMap.mulLeft R (u : A) * (D : Module.End R A) * LinearMap.mulLeft R ((u⁻¹ : Aˣ) : A) =
      (D : Module.End R A) - LinearMap.mulLeft R ((u⁻¹ : Aˣ) * D u) := by
  ext b
  simp [leibniz, D.leibniz_of_mul_eq_one u.inv_mul, mul_add, sq, ← mul_assoc, mul_comm _ b,
    sub_eq_neg_add]

section CompatibleDerivations
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
attribute [local instance 100] LieRing.ofAssociativeRing
namespace Compatible
end Compatible
end CompatibleDerivations
end LieStructures
end Derivation
