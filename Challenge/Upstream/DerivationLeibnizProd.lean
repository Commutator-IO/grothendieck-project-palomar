module

public import Mathlib

@[expose] public section

open Algebra

namespace Derivation

section

variable {R : Type*} {A : Type*} {B : Type*} {M : Type*}

variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [AddCommMonoid M]

variable [Algebra R A] [Algebra R B]

variable [Module A M] [Module B M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

/-- The Leibniz rule for a finite product. -/
theorem leibniz_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, leibniz, ih, Finset.erase_insert ha,
      Finset.smul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [smul_smul, Finset.erase_insert_of_ne (by grind), Finset.prod_insert (by grind)]

end

section

variable {R : Type*} [CommRing R]

variable {A : Type*} [CommRing A] [Algebra R A]

section

variable {M : Type*} [AddCommGroup M] [Module A M] [Module R M]

variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (a b : A)

/-- The Leibniz rule for integer powers of a unit. See `Derivation.leibniz_zpow` for fields. -/
theorem leibniz_zpow_units (u : Aˣ) (n : ℤ) :
    D ↑(u ^ n) = n • ((u ^ (n - 1) : Aˣ) : A) • D ↑u := by
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, leibniz_pow,
      ← natCast_zsmul]
    rcases k with _ | k <;> simp
  · simp only [Int.negSucc_sub_one, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [leibniz_pow, D.leibniz_of_mul_eq_one (Units.inv_mul u), ← Nat.cast_smul_eq_nsmul A,
      ← Int.cast_smul_eq_zsmul A, Nat.add_sub_cancel]
    simp only [smul_smul]
    congr 1
    push_cast
    ring

end

end

end Derivation
