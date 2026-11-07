module

public import Mathlib

@[expose] public section

namespace Folder62

variable {K : Type*} [Field K]

/-- The numerator `(t + 1)(2t − 1)(t − 2)` of (10). -/
def num (t : K) : K := (t + 1) * (2 * t - 1) * (t - 2)

/-- The denominator `t(t − 1)` of (10). -/
def den (t : K) : K := t * (t - 1)

/-- The invariant (11): `j(t) = −(1/27) (num t / den t)²`. -/
noncomputable def j (t : K) : K := -(1 / 27) * (num t / den t) ^ 2

/-- **The fibres of `j` are the `𝔖₃`-orbits.** For `s, t ∉ {0, 1}` in a field where `6` is
invertible, `j s = j t` iff `s` is one of the six anharmonic images of `t`. -/
theorem j_eq_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    j s = j t ↔ s = t ∨ s = 1 / t ∨ s = 1 - t ∨ s = t / (t - 1) ∨ s = 1 / (1 - t) ∨
      s = (t - 1) / t := by
  sorry

end Folder62
