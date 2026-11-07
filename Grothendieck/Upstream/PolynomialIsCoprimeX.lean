module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/polynomial-isCoprime-X`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/polynomial-isCoprime-X`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/Algebra/Polynomial/RingDivision.lean` -/

section
noncomputable section
open Polynomial
namespace Polynomial
universe u v w z
variable {R : Type u} {S : Type v} {a b : R} {n : ℕ}
section CommRing
variable [CommRing R] {p q : R[X]}
section
variable [Semiring S]
end
section
variable [Ring S]
end
end CommRing
section NoZeroDivisors
variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}
end NoZeroDivisors
section CommRing
variable [CommRing R]
section nonZeroDivisors
open scoped nonZeroDivisors
end nonZeroDivisors
theorem isCoprime_X_sub_C_iff {p : R[X]} :
    IsCoprime (X - C a) p ↔ IsUnit (p.eval a) := by
  refine ⟨fun h ↦ by simpa [isCoprime_zero_left] using h.map (evalRingHom a), fun h ↦ ?_⟩
  have ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := p)
  rw [eq_add_of_sub_eq' hq]
  simp [isCoprime_one_right.of_isCoprime_of_dvd_right, h]

@[simp]
theorem isCoprime_X_sub_C_iff_isUnit_sub :
    IsCoprime (X - C a) (X - C b) ↔ IsUnit (a - b) := by
  simp [isCoprime_X_sub_C_iff]

theorem isCoprime_X_iff {p : R[X]} : IsCoprime X p ↔ IsUnit (p.coeff 0) := by
  simpa [coeff_zero_eq_eval_zero] using isCoprime_X_sub_C_iff (a := 0) (p := p)

variable [IsDomain R] {p q : R[X]}
end CommRing
end Polynomial
end

/-! ## From `Mathlib/Analysis/Complex/Polynomial/Basic.lean` -/

section
open Polynomial Bornology Complex
open scoped ComplexConjugate
namespace Complex
end Complex
namespace Polynomial.Gal
section Rationals
attribute [local instance] splits_ℚ_ℂ
attribute [local ext] Complex.ext
end Rationals
end Polynomial.Gal
end
end
