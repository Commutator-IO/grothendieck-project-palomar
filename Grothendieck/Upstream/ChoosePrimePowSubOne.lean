module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `choose-prime-pow-sub-one`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `choose-prime-pow-sub-one`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/Data/Nat/Choose/Lucas.lean` -/

open Finset hiding choose
open Nat Polynomial
namespace Choose
variable {n k a b p : ℕ} [Fact p.Prime]
/-- For primes `p` and `k ≤ p ^ a - 1`, `choose (p ^ a - 1) k` is congruent to `(-1) ^ k`
modulo `p`. -/
theorem choose_pow_sub_one_modEq_neg_one_pow (hk : k ≤ p ^ a - 1) :
    choose (p ^ a - 1) k ≡ (-1) ^ k [ZMOD p] := by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    have h := (Fact.out : p.Prime).dvd_choose_pow (n := a) k.succ_ne_zero (by lia)
    rw [← Nat.sub_add_cancel (by lia : 1 ≤ p ^ a), choose_succ_succ'] at h
    simpa [pow_succ] using (Int.natCast_dvd_natCast.2 h).modEq_zero_int.sub (ih (by lia))

/-- For primes `p` and `k ≤ p ^ a - 1`, `p` does not divide `choose (p ^ a - 1) k`. -/
theorem not_dvd_choose_pow_sub_one (hk : k ≤ p ^ a - 1) : ¬ p ∣ choose (p ^ a - 1) k := fun h ↦
  (Fact.out : p.Prime).not_dvd_one <| by
    simpa [Int.natCast_dvd] using ((Int.natCast_dvd_natCast.2 h).modEq_zero_int.symm.trans
      (choose_pow_sub_one_modEq_neg_one_pow hk)).dvd

end Choose
