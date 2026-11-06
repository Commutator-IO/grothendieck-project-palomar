module

public import Mathlib

public section


/-!
# Folder 62, pages 35–47: the invariant `j` of a conic with an étale trisection

The modernised reading `transcripts/62/62.modern.tex` (« Formules explicites », pages 35
to 39, and « Coniques munies d'une trisection étale », pages 41 to 47) puts the trisection
at `{0, 1, ∞}`, where the six anharmonic substitutions `t, 1/t, 1 − t, t/(t − 1),
1/(1 − t), (t − 1)/t` act as `𝔖₃`, and computes the quotient map (11)

  `j(t) = −(1/27) ((t + 1)(2t − 1)(t − 2) / (t(t − 1)))²`,

a Galois covering of group `𝔖₃` unramified over `P¹ ∖ {0, 1, ∞}`; `j = 0` on the orbit
`{−1, 2, 1/2}`, `j = 1` at the roots of `t² − t + 1`; the involution `κ(t) = (t − 2)/(2t − 1)`
commutes with `𝔖₃` and `j(κt) = 1/j(t)` (12); and `j = 1 − j_cl/1728` with the usual
`j_cl = 256 (t² − t + 1)³/(t²(t − 1)²)`. Where `j(j − 1)` is invertible, the invariant
determines the triple (page 41).

This is finding `62-triples-rigidified-moduli` of `src/content/findings.ts`, fibre by fibre,
over a field `K` in which `6` is invertible, for `t ∉ {0, 1}` (the points off the
trisection).

* `j_sub_j`, `j_eq_iff`: for `s, t ∉ {0, 1}`, `j s − j t` is `4/27` times the product
  of the six factors `s − g(t)`, denominators cleared, divided by `(s(s − 1) t(t − 1))²`; so
  `j s = j t` iff `s` is one of the six images of `t`.
* `j_inv`, `j_one_sub`, `j_div_sub_one`, `j_one_div_one_sub`, `j_sub_one_div`: `j` is
  invariant under the six substitutions.
* `j_eq_zero_iff`, `j_eq_one_iff`: `j t = 0` iff `t ∈ {−1, 2, 1/2}`, `j t = 1` iff
  `t² − t + 1 = 0`.
* `stabilizer_trivial_iff`: `t` is fixed by no non-trivial substitution iff
  `j t ≠ 0` and `j t ≠ 1`: the orbit is free exactly where `j(j − 1)` is invertible.
* `j_eq_one_sub_jcl`: `j = 1 − j_cl/1728`.
* `kappa_kappa`: `κ` is an involution; `j_kappa_mul`: `j(κt) j(t) = 1` (12).

The torsor and barycentre descriptions of pages 49–53, over a base, are not formalised.
-/

namespace Folder62

variable {K : Type*} [Field K]

/-- The numerator `(t + 1)(2t − 1)(t − 2)` of (10). -/
def num (t : K) : K := (t + 1) * (2 * t - 1) * (t - 2)

/-- The denominator `t(t − 1)` of (10). -/
def den (t : K) : K := t * (t - 1)

/-- The invariant (11): `j(t) = −(1/27) (num t / den t)²`. -/
noncomputable def j (t : K) : K := -(1 / 27) * (num t / den t) ^ 2

/-- The involution `κ(t) = (t − 2)/(2t − 1)`. -/
noncomputable def kappa (t : K) : K := (t - 2) / (2 * t - 1)

theorem sub_one_ne {t : K} (ht1 : t ≠ 1) : t - 1 ≠ 0 := sub_ne_zero.2 ht1

theorem one_sub_ne {t : K} (ht1 : t ≠ 1) : 1 - t ≠ 0 := sub_ne_zero.2 (Ne.symm ht1)

theorem den_ne {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) : den t ≠ 0 :=
  mul_ne_zero ht0 (sub_one_ne ht1)

theorem three_pow_ne (h3 : (3 : K) ≠ 0) : (27 : K) ≠ 0 :=
  (by norm_num : (3 : K) ^ 3 = 27) ▸ pow_ne_zero 3 h3

/-- `j s − j t` as the product of the six factors `s − g(t)`, denominators cleared. -/
theorem j_sub_j (h3 : (3 : K) ≠ 0) {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) :
    j s - j t = 4 / 27 * ((s - t) * ((1 - t) * s - 1) * (t * s - t + 1) *
      ((t * s - 1) * (s + t - 1) * ((t - 1) * s - t))) / (den s ^ 2 * den t ^ 2) := by
  have hDs := den_ne hs0 hs1
  have hDt := den_ne ht0 ht1
  have := three_pow_ne h3
  simp only [j]
  field_simp
  simp only [num, den]
  ring

/-- **The fibres of `j` are the `𝔖₃`-orbits.** For `s, t ∉ {0, 1}` in a field where `6` is
invertible, `j s = j t` iff `s` is one of the six anharmonic images of `t`. -/
theorem j_eq_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    j s = j t ↔ s = t ∨ s = 1 / t ∨ s = 1 - t ∨ s = t / (t - 1) ∨ s = 1 / (1 - t) ∨
      s = (t - 1) / t := by
  have h1 := sub_one_ne ht1
  have h1' := one_sub_ne ht1
  have hc : (4 / 27 : K) ≠ 0 :=
    div_ne_zero ((by norm_num : (2 : K) ^ 2 = 4) ▸ pow_ne_zero 2 h2) (three_pow_ne h3)
  have hd : den s ^ 2 * den t ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (den_ne hs0 hs1)) (pow_ne_zero 2 (den_ne ht0 ht1))
  rw [← sub_eq_zero, j_sub_j h3 hs0 hs1 ht0 ht1, div_eq_zero_iff, or_iff_left hd,
    mul_eq_zero, or_iff_right hc]
  have f2 : (1 - t) * s - 1 = 0 ↔ s = 1 / (1 - t) := by
    rw [eq_div_iff h1', sub_eq_zero, mul_comm]
  have f3 : t * s - t + 1 = 0 ↔ s = (t - 1) / t := by
    rw [eq_div_iff ht0]
    exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have f4 : t * s - 1 = 0 ↔ s = 1 / t := by
    rw [eq_div_iff ht0, sub_eq_zero, mul_comm]
  have f5 : s + t - 1 = 0 ↔ s = 1 - t :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have f6 : (t - 1) * s - t = 0 ↔ s = t / (t - 1) := by
    rw [eq_div_iff h1, sub_eq_zero, mul_comm]
  simp only [mul_eq_zero, sub_eq_zero (a := s), f2, f3, f4, f5, f6, or_assoc, or_comm,
    or_left_comm]

section

variable (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
include h2 h3 ht0 ht1

theorem j_inv : j (1 / t) = j t :=
  (j_eq_iff h2 h3 (one_div_ne_zero ht0)
    (fun h => ht1 ((div_eq_one_iff_eq ht0).1 h).symm) ht0 ht1).2 (Or.inr (Or.inl rfl))

theorem j_one_sub : j (1 - t) = j t :=
  (j_eq_iff h2 h3 (fun h => ht1 (by linear_combination -h))
    (fun h => ht0 (by linear_combination -h)) ht0 ht1).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem j_div_sub_one : j (t / (t - 1)) = j t := by
  have h1 := sub_one_ne ht1
  refine (j_eq_iff h2 h3 (div_ne_zero ht0 h1) (fun h => ?_) ht0 ht1).2
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [div_eq_one_iff_eq h1] at h
  exact one_ne_zero (by linear_combination h : (1 : K) = 0)

theorem j_one_div_one_sub : j (1 / (1 - t)) = j t := by
  have h1' := one_sub_ne ht1
  refine (j_eq_iff h2 h3 (one_div_ne_zero h1') (fun h => ?_) ht0 ht1).2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rw [div_eq_one_iff_eq h1'] at h
  exact ht0 (by linear_combination h)

theorem j_sub_one_div : j ((t - 1) / t) = j t := by
  have h1 := sub_one_ne ht1
  refine (j_eq_iff h2 h3 (div_ne_zero h1 ht0) (fun h => ?_) ht0 ht1).2
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  rw [div_eq_one_iff_eq ht0] at h
  exact one_ne_zero (by linear_combination -h : (1 : K) = 0)

end

/-- `j t = 0` iff `t ∈ {−1, 2, 1/2}` (`t ∉ {0, 1}`). -/
theorem j_eq_zero_iff (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    j t = 0 ↔ t = -1 ∨ t = 2 ∨ 2 * t = 1 := by
  have h27 := three_pow_ne h3
  rw [j, mul_eq_zero, div_pow, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero,
    pow_eq_zero_iff two_ne_zero, or_iff_left (den_ne ht0 ht1), num]
  simp only [neg_eq_zero, one_div, inv_eq_zero, h27, false_or, mul_eq_zero,
    add_eq_zero_iff_eq_neg, sub_eq_zero]
  tauto

/-- `1 − j = (4/27) (t² − t + 1)³ / (t(t − 1))²`. -/
theorem one_sub_j (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    1 - j t = 4 / 27 * (t ^ 2 - t + 1) ^ 3 / den t ^ 2 := by
  have := den_ne ht0 ht1
  have := three_pow_ne h3
  simp only [j]
  field_simp
  simp only [num, den]
  ring

/-- `j t = 1` iff `t² − t + 1 = 0` (`t ∉ {0, 1}`, `6` invertible). -/
theorem j_eq_one_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) : j t = 1 ↔ t ^ 2 - t + 1 = 0 := by
  have h4 : (4 / 27 : K) ≠ 0 :=
    div_ne_zero ((by norm_num : (2 : K) ^ 2 = 4) ▸ pow_ne_zero 2 h2) (three_pow_ne h3)
  rw [eq_comm, ← sub_eq_zero, one_sub_j h3 ht0 ht1, div_eq_zero_iff,
    or_iff_left (pow_ne_zero 2 (den_ne ht0 ht1)), mul_eq_zero, or_iff_right h4,
    pow_eq_zero_iff (by norm_num)]

/-- **The orbit is free exactly where `j(j − 1)` is invertible.** For `t ∉ {0, 1}` in a
field where `6` is invertible, no non-trivial anharmonic substitution fixes `t` iff
`j t ≠ 0` and `j t ≠ 1`. -/
theorem stabilizer_trivial_iff (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) :
    (1 / t ≠ t ∧ 1 - t ≠ t ∧ t / (t - 1) ≠ t ∧ 1 / (1 - t) ≠ t ∧ (t - 1) / t ≠ t) ↔
      j t ≠ 0 ∧ j t ≠ 1 := by
  have h1 := sub_one_ne ht1
  have h1' := one_sub_ne ht1
  have e1 : 1 / t = t ↔ t = -1 := by
    rw [div_eq_iff ht0, eq_comm (a := (1 : K)), mul_self_eq_one_iff, or_iff_right ht1]
  have e2 : 1 - t = t ↔ 2 * t = 1 := ⟨fun h => by linear_combination -h, fun h => by
    linear_combination -h⟩
  have e3 : t / (t - 1) = t ↔ t = 2 := by
    rw [div_eq_iff h1, eq_comm (b := t * (t - 1)), mul_eq_left₀ ht0, sub_eq_iff_eq_add,
      one_add_one_eq_two]
  have e4 : 1 / (1 - t) = t ↔ t ^ 2 - t + 1 = 0 := by
    rw [div_eq_iff h1']
    exact ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have e5 : (t - 1) / t = t ↔ t ^ 2 - t + 1 = 0 := by
    rw [div_eq_iff ht0]
    exact ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  simp only [ne_eq, j_eq_zero_iff h3 ht0 ht1, j_eq_one_iff h2 h3 ht0 ht1, e1, e2, e3, e4, e5]
  tauto

/-- `j = 1 − j_cl/1728`, `j_cl = 256 (t² − t + 1)³ / (t²(t − 1)²)` (`t ∉ {0, 1}`). -/
theorem j_eq_one_sub_jcl (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) :
    j t = 1 - 256 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2) / 1728 := by
  have h1728 : (1728 : K) = 64 * 27 := by norm_num
  have h64 : (64 : K) ≠ 0 := (by norm_num : (2 : K) ^ 6 = 64) ▸ pow_ne_zero 6 h2
  have hd : t ^ 2 * (t - 1) ^ 2 = den t ^ 2 := (mul_pow _ _ 2).symm
  rw [hd, h1728, ← sub_sub_cancel 1 (j t), one_sub_j h3 ht0 ht1]
  have := den_ne ht0 ht1
  have := three_pow_ne h3
  field_simp
  ring

/-- `κ` is an involution (`2t ≠ 1`, `3` invertible). -/
theorem kappa_kappa (h3 : (3 : K) ≠ 0) {t : K} (ht : 2 * t - 1 ≠ 0) : kappa (kappa t) = t := by
  have hk : kappa t * (2 * t - 1) = t - 2 := div_mul_cancel₀ _ ht
  have h2k : 2 * kappa t - 1 ≠ 0 := fun h => h3 (by linear_combination 2 * hk - (2 * t - 1) * h)
  change (kappa t - 2) / (2 * kappa t - 1) = t
  rw [div_eq_iff h2k]
  linear_combination -hk

/-- (12): `j(κt) · j(t) = 1` for `t ∉ {0, 1, −1, 2, 1/2}`. -/
theorem j_kappa_mul (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t + 1 ≠ 0)
    (ht2 : t - 2 ≠ 0) (ht : 2 * t - 1 ≠ 0) : j (kappa t) * j t = 1 := by
  set k := kappa t with hkdef
  have hk : k * (2 * t - 1) = t - 2 := div_mul_cancel₀ _ ht
  have hk0 : k ≠ 0 := div_ne_zero ht2 ht
  have hk1 : k ≠ 1 := fun h => htm (by linear_combination hk - (2 * t - 1) * h)
  have hA : num k * (2 * t - 1) ^ 3 = 27 * den t := by
    have e1 : (k + 1) * (2 * t - 1) = 3 * (t - 1) := by linear_combination hk
    have e2 : (2 * k - 1) * (2 * t - 1) = -3 := by linear_combination 2 * hk
    have e3 : (k - 2) * (2 * t - 1) = -3 * t := by linear_combination hk
    calc num k * (2 * t - 1) ^ 3
        = ((k + 1) * (2 * t - 1)) * ((2 * k - 1) * (2 * t - 1)) * ((k - 2) * (2 * t - 1)) := by
          simp only [num]; ring
      _ = 27 * den t := by rw [e1, e2, e3]; simp only [den]; ring
  have hB : den k * (2 * t - 1) ^ 2 = -((t + 1) * (t - 2)) := by
    have e4 : (k - 1) * (2 * t - 1) = -(t + 1) := by linear_combination hk
    calc den k * (2 * t - 1) ^ 2 = (k * (2 * t - 1)) * ((k - 1) * (2 * t - 1)) := by
          simp only [den]; ring
      _ = -((t + 1) * (t - 2)) := by rw [hk, e4]; ring
  have key : num k * num t = -27 * (den k * den t) := by
    refine mul_right_cancel₀ (pow_ne_zero 3 ht) ?_
    rw [show num t = (t + 1) * (2 * t - 1) * (t - 2) from rfl]
    linear_combination (t + 1) * (2 * t - 1) * (t - 2) * hA + 27 * den t * (2 * t - 1) * hB
  have hDk := den_ne hk0 hk1
  have hDt := den_ne ht0 ht1
  have h27 := three_pow_ne h3
  simp only [j]
  field_simp
  linear_combination (num k * num t - 27 * (den k * den t)) * key

end Folder62
