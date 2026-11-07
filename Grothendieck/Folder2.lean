module

public import Mathlib
public import Grothendieck.Upstream.DerivationLeibnizProd

@[expose] public section


/-!
# Folder 2, pages 9 and 13: a nonzero class with trivial total Chern class

The modernised reading `transcripts/2/2.modern.tex` (« Contre-exemples : la classe de Chern
d'une immersion, et le facteur (r−1)! », pages 9 to 13) computes, for the class `ξ^r` of a
point of `P^r` (`ξ = 1 − L^{-1}`, `ξ^r = Σ (−1)^i binom(r, i) L^{-i}`, `c(L^{-i}) = 1 − iη`),

  `c(ξ^r) = ∏_{i=0}^{r} (1 − iη)^{(−1)^i binom(r,i)} = 1 + (−1)^{r−1} (r−1)! η^r`

in `Ã(P^r) = ℤ[η]/(η^{r+1})` (page 9), and concludes on page 13 that for a divisor `Y`
of class `x'` with `(r−1)! x' = 0`, `c(i_!(O_Y)) = 1`.

This is finding `2-trivial-total-chern-class` of `src/content/findings.ts`. mathlib has
no `K`-group of coherent sheaves and no Chern classes, so what is proved is the algebra of
the two pages, in the splitting-principle model the reading uses: `i_!(O_Y) = [O_Y] ⊗ ξ^r
= Σ_i (−1)^i binom(r, i) ([L^{-i}] − [L^{-i} ⊗ O(−Y)])`, with `c(L^{-i}) = 1 − iη` and
`c(L^{-i} ⊗ O(−Y)) = 1 − y − iη` (`y = x'`, first Chern classes adding), so that

  `c(i_!(O_Y)) = ∏_{i=0}^{r} ((1 − iη) / (1 − y − iη))^{(−1)^i binom(r,i)}`.

Congruences modulo `X^{r+1}` in `A⟦X⟧` are identities in `A[η]/(η^{r+1})`.

* `chernPoint_int` and `chernPoint` (page 9): for `r ≥ 1` and any commutative ring `A`,
  `∏_{i=0}^{r} (1 − iX)^{(−1)^i binom(r,i)} ≡ 1 + (−1)^{r−1} (r−1)! X^r  (mod X^{r+1})`.
  Proof by the logarithmic derivative over `ℤ`: `P'/P = −Σ_m S(m+1) X^m` with
  `S(k) = Σ_i (−1)^i binom(r,i) i^k`, zero for `k < r` and `(−1)^r r!` for `k = r`
  (mathlib's forward differences), then `n p_n = 0` for `n < r` and `r p_r = −S(r)`.
* `chernImmersion` (page 13): for any commutative ring `A` and `y ∈ A` with `1 − y` a unit
  (`y` nilpotent in the geometric case, `chernImmersion_of_isNilpotent`) and
  `(r−1)! · y = 0`, `∏_{i=0}^{r} ((1 − iX)/(1 − y − iX))^{(−1)^i binom(r,i)} ≡ 1`
  modulo `X^{r+1}`. The denominator product is the numerator one rescaled by `(1 − y)^{-1}`,
  so the two agree modulo `X^{r+1}` once `(r−1)! (1 − (1 − y)^{-r}) = 0`.
* `chernRatio`, `chernCurve`, `chernEllipticNB` (the N.B. of page 13, read in the second
  transcription pass): the page itself gives the example, `X` an elliptic curve,
  `x = (a) − (0)` with `a + a = 0`, `a ≠ 0`, and `r = 3`. With `p, q` the classes of the two
  points (`p² = q² = 0` on a curve) and `r! (p − q) = 0`,
  `∏ ((1 − p − iX)/(1 − q − iX))^{(−1)^i binom(r,i)} ≡ 1` modulo `X^{r+1}`; for `r = 3`
  the hypothesis `2(p − q) = 0` given by `a + a = 0` suffices.

That the classes `i_!(O_Y)` and `i_!(x)` are nonzero in `K(X × P^r)`, which the N.B.
asserts, and the restriction `r ≥ 3`, are geometric and not formalised. Page 21 states
`n ≥ 3` for its example itself (« si n − 1 > 1 i.e. n ≥ 3, CK a de la torsion »).
-/

open PowerSeries Finset

namespace Folder2

/-- The exponent `(−1)^i binom(r, i)`. -/
def ε (r i : ℕ) : ℤ := (-1) ^ i * r.choose i

variable {A : Type*} [CommRing A]

/-- The unit `w − aX` of `A⟦X⟧`, for a unit `w` of `A`. -/
noncomputable def lin (w : Aˣ) (a : A) : A⟦X⟧ˣ :=
  (show IsUnit (C (w : A) - C a * X : A⟦X⟧) from
    isUnit_iff_constantCoeff.2 (by simp)).unit

@[simp] theorem coe_lin (w : Aˣ) (a : A) : (lin w a : A⟦X⟧) = C (w : A) - C a * X := rfl

/-- The product `∏_{i=0}^{r} u_i ^ ((−1)^i binom(r, i))`. -/
noncomputable def altProd (r : ℕ) (u : ℕ → A⟦X⟧ˣ) : A⟦X⟧ˣ :=
  ∏ i ∈ range (r + 1), u i ^ ε r i

/-! ### The logarithmic derivative -/

theorem derivative_pow_units (u : A⟦X⟧ˣ) (n : ℕ) :
    d⁄dX (↑(u ^ n) : A⟦X⟧) = n * (↑(u ^ n) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, Derivation.leibniz, ih]
    simp only [smul_eq_mul, Nat.cast_succ]
    linear_combination (-(↑(u ^ n) * d⁄dX (↑u : A⟦X⟧))) * Units.mul_inv u

theorem derivative_zpow_units (u : A⟦X⟧ˣ) (n : ℤ) :
    d⁄dX (↑(u ^ n) : A⟦X⟧) = n * (↑(u ^ n) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) := by
  rw [Derivation.leibniz_zpow_units, zpow_sub_one, Units.val_mul, zsmul_eq_mul, smul_eq_mul]

theorem derivative_prod_units {ι : Type*} (s : Finset ι) (w : ι → A⟦X⟧ˣ) :
    d⁄dX (↑(∏ i ∈ s, w i) : A⟦X⟧) =
      ↑(∏ i ∈ s, w i) * ∑ i ∈ s, ↑(w i)⁻¹ * d⁄dX (↑(w i) : A⟦X⟧) := by
  classical
  rw [Units.coe_prod, Derivation.leibniz_prod, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [smul_eq_mul, ← mul_prod_erase s (fun j => (w j : A⟦X⟧)) hi]
  linear_combination (-((∏ j ∈ s.erase i, (w j : A⟦X⟧)) * d⁄dX (↑(w i) : A⟦X⟧))) *
    Units.mul_inv (w i)

theorem coe_lin_one_inv (a : A) : (↑(lin 1 a)⁻¹ : A⟦X⟧) = mk fun m => a ^ m := by
  rw [Units.inv_eq_of_mul_eq_one_left]
  simpa [rescale_mk, rescale_X, map_sub] using
    congr(rescale a $(mk_one_mul_one_sub_eq_one (S := A)))

theorem eps_mul_pow {r i : ℕ} (k : ℕ) (hi : i ∈ range (r + 1)) :
    ε r i * (i : ℤ) ^ k = (-1) ^ r * ((-1) ^ (r - i) * r.choose i * (i : ℤ) ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (mem_range.1 hi))
  rw [ε, Nat.add_sub_cancel_left, pow_add]
  have hsq : ((-1 : ℤ) ^ j) ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  linear_combination (-((-1 : ℤ) ^ i * ((i + j).choose i : ℤ) * (i : ℤ) ^ k)) * hsq

/-- The sums `S(k) = Σ_i (−1)^i binom(r,i) i^k` vanish for `k < r` (forward differences). -/
theorem sum_eps_pow_of_lt {r k : ℕ} (h : k < r) :
    ∑ i ∈ range (r + 1), ε r i * (i : ℤ) ^ k = 0 := by
  have := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  simp only [Pi.zero_apply, zero_add, nsmul_eq_mul, mul_one, smul_eq_mul] at this
  rw [sum_congr rfl fun i hi => eps_mul_pow k hi, ← mul_sum, this, mul_zero]

/-- `S(r) = (−1)^r r!`. -/
theorem sum_eps_pow_self (r : ℕ) :
    ∑ i ∈ range (r + 1), ε r i * (i : ℤ) ^ r = (-1) ^ r * r.factorial := by
  have := congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := r)) 0
  rw [fwdDiff_iter_eq_sum_shift] at this
  simp only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, smul_eq_mul] at this
  rw [sum_congr rfl fun i hi => eps_mul_pow r hi, ← mul_sum, this]

theorem logDeriv_zpow (u : A⟦X⟧ˣ) (n : ℤ) :
    ↑(u ^ n)⁻¹ * d⁄dX (↑(u ^ n) : A⟦X⟧) = n * (↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) := by
  rw [derivative_zpow_units]
  linear_combination ((n : A⟦X⟧) * ↑u⁻¹ * d⁄dX (↑u : A⟦X⟧)) * Units.inv_mul (u ^ n)

/-! ### Page 9 -/

/-- **Page 9**, over `ℤ`: `∏ (1 − iX)^{(−1)^i binom(r,i)} ≡ 1 + (−1)^{r−1}(r−1)! X^r`
modulo `X^{r+1}`. -/
theorem chernPoint_int {r : ℕ} (hr : 1 ≤ r) :
    X ^ (r + 1) ∣ (↑(altProd r fun i => lin 1 (i : ℤ)) : ℤ⟦X⟧) -
      (1 + C ((-1) ^ (r - 1) * ((r - 1).factorial : ℤ)) * X ^ r) := by
  set P : ℤ⟦X⟧ := ↑(altProd r fun i => lin 1 (i : ℤ)) with hPdef
  set L : ℤ⟦X⟧ := mk fun m => -∑ i ∈ range (r + 1), ε r i * (i : ℤ) ^ (m + 1)
  have hD : derivative (R := ℤ) P = P * L := by
    rw [hPdef, altProd, derivative_prod_units]
    congr 1
    simp only [logDeriv_zpow, coe_lin_one_inv]
    ext m
    have hd (i : ℕ) : derivative (R := ℤ) (↑(lin 1 (i : ℤ)) : ℤ⟦X⟧) = C (-(i : ℤ)) := by
      ext (_ | n) <;> simp
    simp only [hd, L, coeff_mk, map_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← map_intCast (C (R := ℤ)), coeff_C_mul, coeff_mul_C, coeff_mk]
    simp only [Int.cast_id]
    ring
  have hL : ∀ m, m + 1 < r → coeff m L = 0 := fun m hm => by
    simp [L, sum_eps_pow_of_lt hm]
  have hLr : coeff (r - 1) L = -((-1) ^ r * r.factorial) := by
    simp [L, Nat.sub_add_cancel hr, sum_eps_pow_self]
  have hP0 : constantCoeff P = 1 := by
    have := congrArg Units.val (show Units.map (constantCoeff (R := ℤ)).toMonoidHom
        (altProd r fun i => lin 1 (i : ℤ)) = 1 by
      rw [altProd, map_prod]
      exact prod_eq_one fun i _ => by
        rw [map_zpow, show Units.map (constantCoeff (R := ℤ)).toMonoidHom (lin 1 (i : ℤ)) = 1
          from Units.ext (by simp), one_zpow])
    simpa [P] using this
  have hcoef : ∀ n, coeff (n + 1) P * (n + 1) =
      ∑ p ∈ antidiagonal n, coeff p.1 P * coeff p.2 L := fun n => by
    rw [← coeff_derivative, hD, coeff_mul]
  have hlow : ∀ n, n + 1 < r → coeff (n + 1) P = 0 := fun n hn => by
    have h := hcoef n
    rw [sum_eq_zero fun p hp => by
      rw [hL p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega), mul_zero]] at h
    exact (mul_eq_zero.1 h).resolve_right (by positivity)
  have htop : coeff r P = (-1) ^ (r - 1) * ((r - 1).factorial : ℤ) := by
    have hs : ∑ p ∈ antidiagonal (r - 1), coeff p.1 P * coeff p.2 L =
        coeff 0 P * coeff (r - 1) L := by
      refine sum_eq_single_of_mem (0, r - 1) (by simp) fun p hp hne => ?_
      rcases p with ⟨_ | a, b⟩
      · simp_all
      · simp [hL b (by simp at hp; omega)]
    have h := hcoef (r - 1)
    rw [hs, coeff_zero_eq_constantCoeff_apply, hP0, hLr] at h
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hr
    simp only [Nat.add_sub_cancel, Nat.factorial_succ] at h ⊢
    have h' : (coeff (s + 1) P - (-1) ^ s * (s.factorial : ℤ)) * ((s : ℤ) + 1) = 0 := by
      push_cast at h; linear_combination h
    linear_combination (mul_eq_zero.1 h').resolve_right (by positivity)
  refine X_pow_dvd_iff.2 fun m hm => ?_
  rcases m with _ | n
  · simp [hP0, show r ≠ 0 by omega]
  · rw [map_sub, map_add, coeff_C_mul_X_pow, coeff_one]
    rcases (Nat.lt_succ_iff.1 hm).lt_or_eq with h | h
    · simp [hlow n h, h.ne]
    · rw [h, htop]; simp [show r ≠ 0 by omega]

/-- **Page 9**, over any commutative ring `A`: in `A[η]/(η^{r+1})`,
`∏_{i=0}^{r} (1 − iη)^{(−1)^i binom(r,i)} = 1 + (−1)^{r−1}(r−1)! η^r`. -/
theorem chernPoint {r : ℕ} (hr : 1 ≤ r) :
    X ^ (r + 1) ∣ (↑(altProd r fun i => lin 1 (i : A)) : A⟦X⟧) -
      (1 + C ((-1) ^ (r - 1) * ((r - 1).factorial : A)) * X ^ r) := by
  have h := map_dvd (PowerSeries.map (Int.castRingHom A)) (chernPoint_int hr)
  have hP : PowerSeries.map (Int.castRingHom A) ↑(altProd r fun i => lin 1 (i : ℤ)) =
      ↑(altProd r fun i => lin 1 (i : A)) :=
    congrArg Units.val (show Units.map (PowerSeries.map (Int.castRingHom A)).toMonoidHom
        (altProd r fun i => lin 1 (i : ℤ)) = altProd r fun i => lin 1 (i : A) by
      simp only [altProd, map_prod, map_zpow]
      exact prod_congr rfl fun i _ => congrArg (· ^ ε r i) (Units.ext (by simp)))
  rw [map_sub, hP] at h
  simpa [map_add, map_mul, map_pow, map_C, map_X] using h

theorem rescale_C (a c : A) : rescale a (C c) = C c := by
  ext (_ | n) <;> simp [coeff_rescale, coeff_C]

theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {ι : Type*} (c : G) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, c ^ f i = c ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, zpow_add]

/-! ### Page 13 -/

/-- **Page 13.** For `y ∈ A` with `1 − y` a unit and `(r−1)! · y = 0`, in `A[η]/(η^{r+1})`:
`∏_{i=0}^{r} ((1 − iη) / (1 − y − iη))^{(−1)^i binom(r,i)} = 1`, that is
`c(i_!(O_Y)) = 1` in the splitting-principle model, `y = x'`. -/
theorem chernImmersion {r : ℕ} (hr : 1 ≤ r) {y : A} (hy : IsUnit (1 - y))
    (h : ((r - 1).factorial : A) * y = 0) :
    X ^ (r + 1) ∣ (↑(∏ i ∈ range (r + 1),
      (lin 1 (i : A) * (lin hy.unit (i : A))⁻¹) ^ ε r i) : A⟦X⟧) - 1 := by
  set w := hy.unit
  set a : A := ↑w⁻¹
  have haw : a * (1 - y) = 1 := by simp [a, w]
  -- the denominators are the numerators rescaled by `a = (1 − y)⁻¹`
  have hlin (i : ℕ) : lin w (i : A) =
      Units.map (C (R := A)).toMonoidHom w * Units.map (rescale a).toMonoidHom (lin 1 (i : A)) := by
    refine Units.ext ?_
    change C (w : A) - C (i : A) * X = C (w : A) * rescale a (C 1 - C (i : A) * X)
    have hwa : C (w : A) * C a = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [map_sub, map_mul, rescale_C, rescale_C, rescale_X, map_one]
    linear_combination (C (i : A) * X) * hwa
  have hsum : ∑ i ∈ range (r + 1), ε r i = 0 :=
    Int.alternating_sum_range_choose_of_ne (by omega)
  have hQ : altProd r (fun i => lin w (i : A)) =
      Units.map (rescale a).toMonoidHom (altProd r fun i => lin 1 (i : A)) := by
    simp only [altProd, hlin, mul_zpow, prod_mul_distrib, prod_zpow_eq_zpow_sum, hsum, zpow_zero,
      one_mul, map_prod, map_zpow]
  set P : A⟦X⟧ := ↑(altProd r fun i => lin 1 (i : A))
  set c : A := (-1) ^ (r - 1) * ((r - 1).factorial : A)
  have hPc : ∀ n, n < r + 1 → coeff n P = coeff n (1 + C c * X ^ r) := fun n hn =>
    sub_eq_zero.1 (by rw [← map_sub]; exact X_pow_dvd_iff.1 (chernPoint hr) n hn)
  have hca : c * a ^ r = c := by
    have hg := geom_sum_mul (1 - y) r
    have hp : a ^ r * (1 - y) ^ r = 1 := by rw [← mul_pow, haw, one_pow]
    linear_combination (c * a ^ r) * hg + c * hp + ((-1) ^ (r - 1) * a ^ r *
      ∑ i ∈ range r, (1 - y) ^ i) * h
  have hPQ : X ^ (r + 1) ∣ P - (↑(altProd r fun i => lin w (i : A)) : A⟦X⟧) := by
    rw [hQ, Units.coe_map]
    change X ^ (r + 1) ∣ P - rescale a P
    refine X_pow_dvd_iff.2 fun n hn => ?_
    rw [map_sub, coeff_rescale, hPc n hn, map_add, coeff_C_mul_X_pow, coeff_one]
    rcases n with _ | n
    · simp
    · obtain rfl | hnr := eq_or_ne (n + 1) r
      · simp only [↓reduceIte, Nat.succ_ne_zero]
        linear_combination -hca
      · simp [hnr]
  have hprod : ∏ i ∈ range (r + 1), (lin 1 (i : A) * (lin w (i : A))⁻¹) ^ ε r i =
      altProd r (fun i => lin 1 (i : A)) * (altProd r fun i => lin w (i : A))⁻¹ := by
    simp only [altProd, mul_zpow, prod_mul_distrib, inv_zpow, prod_inv_distrib]
  rw [hprod, Units.val_mul]
  convert hPQ.mul_right (↑(altProd r fun i => lin w (i : A))⁻¹ : A⟦X⟧) using 1
  linear_combination Units.mul_inv (altProd r fun i => lin w (i : A))

/-- Page 13 with `y` nilpotent, as `x' ∈ Ã(X)` is. -/
theorem chernImmersion_of_isNilpotent {r : ℕ} (hr : 1 ≤ r) {y : A} (hy : IsNilpotent y)
    (h : ((r - 1).factorial : A) * y = 0) :
    X ^ (r + 1) ∣ (↑(∏ i ∈ range (r + 1),
      (lin 1 (i : A) * (lin hy.isUnit_one_sub.unit (i : A))⁻¹) ^ ε r i) : A⟦X⟧) - 1 :=
  chernImmersion hr hy.isUnit_one_sub h

/-! ### Page 13, the N.B.: a class of degree zero on an elliptic curve

The N.B. of page 13 takes `X` an elliptic curve with origin `0`, a point `a ≠ 0` with
`a + a = 0`, `x = (a) − (0)` and `r = 3`, and states that `y = i_!(x)` is nonzero while
the coefficients of its Chern class vanish. In the splitting-principle model,
`x = [O_a] − [O_0] = [O(−0)] − [O(−a)]` and
`i_!(x) = Σ_i (−1)^i binom(r, i) ([L^{-i} ⊗ O(−0)] − [L^{-i} ⊗ O(−a)])`, with
`c(L^{-i} ⊗ O(−0)) = 1 − p − iη` and `c(L^{-i} ⊗ O(−a)) = 1 − q − iη`, `p, q ∈ A^1(X)` the
classes of the two points: `p² = q² = 0` on a curve, and `a + a = 0` gives `2(p − q) = 0`. -/

/-- The twist by a unit is a rescaling: `∏ (w − iX)^{ε} = ∏ (1 − i w^{-1} X)^{ε}`, the
exponents summing to `0`. -/
theorem altProd_lin {r : ℕ} (hr : 1 ≤ r) (w : Aˣ) :
    altProd r (fun i => lin w (i : A)) =
      Units.map (rescale (↑w⁻¹ : A)).toMonoidHom (altProd r fun i => lin 1 (i : A)) := by
  have hlin (i : ℕ) : lin w (i : A) = Units.map (C (R := A)).toMonoidHom w *
      Units.map (rescale (↑w⁻¹ : A)).toMonoidHom (lin 1 (i : A)) := by
    refine Units.ext ?_
    change C (w : A) - C (i : A) * X = C (w : A) * rescale (↑w⁻¹ : A) (C 1 - C (i : A) * X)
    have hwa : C (w : A) * C (↑w⁻¹ : A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [map_sub, map_mul, rescale_C, rescale_C, rescale_X, map_one]
    linear_combination (C (i : A) * X) * hwa
  have hsum : ∑ i ∈ range (r + 1), ε r i = 0 :=
    Int.alternating_sum_range_choose_of_ne (by omega)
  simp only [altProd, hlin, mul_zpow, prod_mul_distrib, prod_zpow_eq_zpow_sum, hsum, zpow_zero,
    one_mul, map_prod, map_zpow]

/-- **Page 13**, two twists: for units `u, v` of `A` with `(r−1)! (u^{-r} − v^{-r}) = 0`,
`∏_{i=0}^{r} ((u − iη)/(v − iη))^{(−1)^i binom(r,i)} = 1` in `A[η]/(η^{r+1})`. -/
theorem chernRatio {r : ℕ} (hr : 1 ≤ r) (u v : Aˣ)
    (h : ((r - 1).factorial : A) * ((↑u⁻¹ : A) ^ r - (↑v⁻¹ : A) ^ r) = 0) :
    X ^ (r + 1) ∣ (↑(∏ i ∈ range (r + 1),
      (lin u (i : A) * (lin v (i : A))⁻¹) ^ ε r i) : A⟦X⟧) - 1 := by
  set P : A⟦X⟧ := ↑(altProd r fun i => lin 1 (i : A))
  set c : A := (-1) ^ (r - 1) * ((r - 1).factorial : A)
  have hPc : ∀ n, n < r + 1 → coeff n P = coeff n (1 + C c * X ^ r) := fun n hn =>
    sub_eq_zero.1 (by rw [← map_sub]; exact X_pow_dvd_iff.1 (chernPoint hr) n hn)
  have hPQ : X ^ (r + 1) ∣ (↑(altProd r fun i => lin u (i : A)) : A⟦X⟧) -
      (↑(altProd r fun i => lin v (i : A)) : A⟦X⟧) := by
    rw [altProd_lin hr u, altProd_lin hr v, Units.coe_map, Units.coe_map]
    change X ^ (r + 1) ∣ rescale (↑u⁻¹ : A) P - rescale (↑v⁻¹ : A) P
    refine X_pow_dvd_iff.2 fun n hn => ?_
    rw [map_sub, coeff_rescale, coeff_rescale, hPc n hn, map_add, coeff_C_mul_X_pow, coeff_one]
    rcases n with _ | n
    · simp
    · obtain rfl | hnr := eq_or_ne (n + 1) r
      · simp only [↓reduceIte, Nat.succ_ne_zero, zero_add]
        linear_combination (-1) ^ (n + 1 - 1) * h
      · simp [hnr]
  have hprod : ∏ i ∈ range (r + 1), (lin u (i : A) * (lin v (i : A))⁻¹) ^ ε r i =
      altProd r (fun i => lin u (i : A)) * (altProd r fun i => lin v (i : A))⁻¹ := by
    simp only [altProd, mul_zpow, prod_mul_distrib, inv_zpow, prod_inv_distrib]
  rw [hprod, Units.val_mul]
  convert hPQ.mul_right (↑(altProd r fun i => lin v (i : A))⁻¹ : A⟦X⟧) using 1
  linear_combination Units.mul_inv (altProd r fun i => lin v (i : A))

theorem one_add_pow_of_sq_eq_zero {p : A} (hp : p ^ 2 = 0) (n : ℕ) :
    (1 + p) ^ n = 1 + n * p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (n : A) * hp

/-- `(1 − p)^{-1} = 1 + p` when `p² = 0`. -/
theorem inv_one_sub_of_sq_eq_zero {p : A} (hp : p ^ 2 = 0) :
    (↑(IsNilpotent.isUnit_one_sub ⟨2, hp⟩ : IsUnit (1 - p)).unit⁻¹ : A) = 1 + p := by
  rw [Units.inv_eq_of_mul_eq_one_left]
  simp only [IsUnit.unit_spec]
  linear_combination -hp

/-- **Page 13, N.B.**, on a curve: for `p, q` with `p² = q² = 0` and `r! (p − q) = 0`,
`∏_{i=0}^{r} ((1 − p − iη)/(1 − q − iη))^{(−1)^i binom(r,i)} = 1` in `A[η]/(η^{r+1})`,
that is `c(i_!(x)) = 1` for `x = [O(−0)] − [O(−a)]`. -/
theorem chernCurve {r : ℕ} (hr : 1 ≤ r) {p q : A} (hp : p ^ 2 = 0) (hq : q ^ 2 = 0)
    (h : (r.factorial : A) * (p - q) = 0) :
    X ^ (r + 1) ∣ (↑(∏ i ∈ range (r + 1),
      (lin (IsNilpotent.isUnit_one_sub ⟨2, hp⟩ : IsUnit (1 - p)).unit (i : A) *
        (lin (IsNilpotent.isUnit_one_sub ⟨2, hq⟩ : IsUnit (1 - q)).unit (i : A))⁻¹) ^
          ε r i) : A⟦X⟧) - 1 := by
  refine chernRatio hr _ _ ?_
  rw [inv_one_sub_of_sq_eq_zero hp, inv_one_sub_of_sq_eq_zero hq,
    one_add_pow_of_sq_eq_zero hp, one_add_pow_of_sq_eq_zero hq]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [Nat.factorial_succ] at h
  simp only [Nat.add_sub_cancel]
  push_cast at h ⊢
  linear_combination h

/-- **Page 13, N.B.**, the example of the page: `r = 3` and `2(p − q) = 0` (a point `a ≠ 0`
with `a + a = 0` on an elliptic curve) give `c(i_!(x)) = 1` in `A[η]/(η^4)`. -/
theorem chernEllipticNB {p q : A} (hp : p ^ 2 = 0) (hq : q ^ 2 = 0) (h : 2 * (p - q) = 0) :
    X ^ (3 + 1) ∣ (↑(∏ i ∈ range (3 + 1),
      (lin (IsNilpotent.isUnit_one_sub ⟨2, hp⟩ : IsUnit (1 - p)).unit (i : A) *
        (lin (IsNilpotent.isUnit_one_sub ⟨2, hq⟩ : IsUnit (1 - q)).unit (i : A))⁻¹) ^
          ε 3 i) : A⟦X⟧) - 1 :=
  chernCurve (by norm_num) hp hq (by
    rw [show ((Nat.factorial 3 : ℕ) : A) = 3 * 2 by norm_num [Nat.factorial]]
    linear_combination 3 * h)

/-! ### Page 21: `φ_K` is not injective for `K = K(P^{n−1})`, `n ≥ 3`

`K = ℤ[L]/(L − 1)^n = ℤ[ξ]/(ξ^n)` with `ξ = 1 − L^{-1}`, `L` the only geometric element.
Its Chern ring `CK` is generated by `ζ = c¹(L)`, with `c(L^{-i}) = 1 − iζ`, subject to
`c(ξ^n) = 1`, i.e. to the vanishing of the homogeneous components of positive degree of
`c(ξ^n) = ∏_{i=0}^{n} (1 − iζ)^{(−1)^i binom(n,i)}` (the relation `(L − 1)^n = 0` and
`ξ^n = 0` generate the same ideal, `L` being a unit). Its `γ`-graded ring is
`GK = ℤ[ζ]/(ζ^n)`. -/

section Page21

/-- `c(ξ^n) = ∏_{i=0}^{n} (1 − iζ)^{(−1)^i binom(n,i)}`, in `ℤ⟦ζ⟧`. -/
noncomputable def cXi (n : ℕ) : ℤ⟦X⟧ := ↑(altProd n fun i => lin 1 (i : ℤ))

theorem coeff_cXi {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    coeff m (cXi n) = coeff m (1 + C ((-1) ^ (n - 1) * ((n - 1).factorial : ℤ)) * X ^ n) := by
  have h := X_pow_dvd_iff.1 (chernPoint_int hn) m (by omega)
  rw [map_sub] at h
  exact sub_eq_zero.1 h

theorem coeff_cXi_of_lt {n m : ℕ} (hn : 1 ≤ n) (h1 : 1 ≤ m) (hm : m < n) :
    coeff m (cXi n) = 0 := by
  rw [coeff_cXi hn hm.le, map_add, coeff_C_mul_X_pow, coeff_one]
  simp [show m ≠ 0 by omega, hm.ne]

theorem coeff_cXi_self {n : ℕ} (hn : 1 ≤ n) :
    coeff n (cXi n) = (-1) ^ (n - 1) * ((n - 1).factorial : ℤ) := by
  rw [coeff_cXi hn le_rfl, map_add, coeff_C_mul_X_pow, coeff_one]
  simp [show n ≠ 0 by omega]

/-- The relations of `CK`: the components `c^m(ξ^n) ζ^m`, `m ≥ 1`. -/
noncomputable def relIdeal (n : ℕ) : Ideal (Polynomial ℤ) :=
  Ideal.span (Set.range fun m : ℕ =>
    Polynomial.C (coeff (m + 1) (cXi n)) * Polynomial.X ^ (m + 1))

/-- The Chern ring `CK` of `K = K(P^{n−1})` with `L` geometric. -/
abbrev CK (n : ℕ) := Polynomial ℤ ⧸ relIdeal n

/-- The graded ring `GK = ℤ[ζ]/(ζ^n)`. -/
abbrev GK (n : ℕ) := Polynomial ℤ ⧸ Ideal.span {(Polynomial.X : Polynomial ℤ) ^ n}

/-- `ζ = c¹(L)` in `CK`. -/
noncomputable def ζ (n : ℕ) : CK n := Ideal.Quotient.mk _ Polynomial.X

theorem relIdeal_le {n : ℕ} (hn : 1 ≤ n) :
    relIdeal n ≤ Ideal.span {(Polynomial.X : Polynomial ℤ) ^ n} := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨m, rfl⟩
  rcases lt_or_ge (m + 1) n with h | h
  · simp [coeff_cXi_of_lt hn (by omega) h]
  · exact Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_right (pow_dvd_pow _ h) _)

/-- `φ_K : CK → GK`, `c¹(L) ↦ ζ`. -/
noncomputable def φ {n : ℕ} (hn : 1 ≤ n) : CK n →+* GK n := Ideal.Quotient.factor (relIdeal_le hn)

theorem φ_surjective {n : ℕ} (hn : 1 ≤ n) : Function.Surjective (φ hn) :=
  Ideal.Quotient.factor_surjective (relIdeal_le hn)

/-- **Page 21.** `(n − 1)! ζ^n = 0` in `CK`. -/
theorem factorial_mul_ζ_pow {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1).factorial : CK n) * ζ n ^ n = 0 := by
  have hmem : Polynomial.C (coeff n (cXi n)) * Polynomial.X ^ n ∈ relIdeal n :=
    Ideal.subset_span ⟨n - 1, by dsimp only; rw [Nat.sub_add_cancel hn]⟩
  have h := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  rw [coeff_cXi_self hn] at h
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast] at h
  rw [ζ]
  have hu : ((-1 : CK n) ^ (n - 1)) * (-1) ^ (n - 1) = 1 := by
    rw [← mul_pow]; norm_num
  calc ((n - 1).factorial : CK n) * Ideal.Quotient.mk _ Polynomial.X ^ n
      = ((-1) ^ (n - 1) * (-1) ^ (n - 1)) *
          (((n - 1).factorial : CK n) * Ideal.Quotient.mk _ Polynomial.X ^ n) := by
        rw [hu, one_mul]
    _ = (-1) ^ (n - 1) * ((-1) ^ (n - 1) * ((n - 1).factorial : CK n) *
          Ideal.Quotient.mk _ Polynomial.X ^ n) := by ring
    _ = 0 := by rw [h, mul_zero]

/-- `GK = ℤ[ζ]/(ζ^n)` has no `ℤ`-torsion. -/
theorem GK_torsionFree {n : ℕ} {k : ℤ} (hk : k ≠ 0) {y : GK n} (h : (k : GK n) * y = 0) :
    y = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_intCast (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℤ) ^ n})) k,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro d hd
  have := h d hd
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hk

/-- The test ring `(ℤ/(n−1)!)[h]/(h^{n+1})`, as a quotient of power series. -/
abbrev T (n : ℕ) :=
  (ZMod (n - 1).factorial)⟦X⟧ ⧸ Ideal.span {(X : (ZMod (n - 1).factorial)⟦X⟧) ^ (n + 1)}

/-- `h = c¹(L)` in the test ring. -/
noncomputable def hT (n : ℕ) : T n := Ideal.Quotient.mk _ X

theorem natCast_factorial_T (n : ℕ) : ((n - 1).factorial : T n) = 0 := by
  rw [← map_natCast ((Ideal.Quotient.mk _).comp (C (R := ZMod (n - 1).factorial))),
    ZMod.natCast_self, map_zero]

theorem hT_pow_eq_zero {n m : ℕ} (hm : n + 1 ≤ m) : hT n ^ m = 0 := by
  rw [hT, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ hm

theorem hT_pow_ne_zero {n : ℕ} (hn : 3 ≤ n) : hT n ^ n ≠ 0 := by
  have : Fact (1 < (n - 1).factorial) :=
    ⟨lt_of_lt_of_le (by omega) (Nat.self_le_factorial (n - 1))⟩
  rw [hT, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff]
  intro h
  simpa using h n (by omega)

/-- **The settling computation.** For `n ≥ 3` there is a Chern homomorphism on
`K(P^{n−1})` with `c(L^{-i}) = 1 − ih`, `c(ξ^n) = 1`, and `h^n ≠ 0`, `(n−1)! h^n = 0`. -/
theorem exists_chern {n : ℕ} (hn : 3 ≤ n) :
    Ideal.Quotient.mk _ (↑(altProd n fun i => lin 1 (i : ZMod (n - 1).factorial)) :
        (ZMod (n - 1).factorial)⟦X⟧) = (1 : T n) ∧
      hT n ^ n ≠ 0 ∧ ((n - 1).factorial : T n) * hT n ^ n = 0 := by
  refine ⟨?_, hT_pow_ne_zero hn, by rw [natCast_factorial_T, zero_mul]⟩
  have h := chernPoint (A := ZMod (n - 1).factorial) (r := n) (by omega)
  rw [ZMod.natCast_self, mul_zero, map_zero, zero_mul, add_zero] at h
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact h

/-- The Chern homomorphism `CK → T`, `ζ ↦ h`. -/
noncomputable def toT {n : ℕ} (hn : 1 ≤ n) : CK n →+* T n :=
  Ideal.Quotient.lift (relIdeal n) (Polynomial.eval₂RingHom (Int.castRingHom (T n)) (hT n)) (by
    intro f hf
    refine Submodule.span_induction (p := fun f _ =>
      Polynomial.eval₂RingHom (Int.castRingHom (T n)) (hT n) f = 0) ?_ (by simp)
      (fun _ _ _ _ h1 h2 => by rw [map_add, h1, h2, add_zero])
      (fun a _ _ h => by rw [smul_eq_mul, map_mul, h, mul_zero]) hf
    rintro _ ⟨m, rfl⟩
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow]
    simp only [eq_intCast]
    rcases lt_trichotomy (m + 1) n with h | h | h
    · rw [coeff_cXi_of_lt hn (by omega) h, Int.cast_zero, zero_mul]
    · rw [h, coeff_cXi_self hn]
      push_cast
      rw [natCast_factorial_T, mul_zero, zero_mul]
    · rw [hT_pow_eq_zero (by omega), mul_zero])

theorem toT_ζ {n : ℕ} (hn : 1 ≤ n) : toT hn (ζ n) = hT n := by
  simp [toT, ζ]

/-- **Page 21**, completed: for `n ≥ 3`, `ζ^n ≠ 0` in `CK`, so `CK` has torsion. -/
theorem ζ_pow_ne_zero {n : ℕ} (hn : 3 ≤ n) : ζ n ^ n ≠ 0 := by
  intro h
  have := congrArg (toT (by omega : 1 ≤ n)) h
  rw [map_pow, toT_ζ, map_zero] at this
  exact hT_pow_ne_zero hn this

/-- **Page 21.** For `n ≥ 3`, `φ_K : CK → GK` is surjective and not injective: `ζ^n` is a
nonzero torsion element of `CK`, killed by `(n − 1)!`, while `GK` is torsion-free. -/
theorem φ_not_injective {n : ℕ} (hn : 3 ≤ n) :
    ¬ Function.Injective (φ (Nat.le_trans (Nat.le_add_left 1 2) hn)) := by
  intro hinj
  refine ζ_pow_ne_zero hn (hinj ?_)
  rw [map_zero, map_pow, ζ, φ, Ideal.Quotient.factor_mk, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- For `n ≤ 2` the factor `(n − 1)!` is `1`: `ζ^n = 0` in `CK` and `φ_K` is bijective. -/
theorem φ_bijective_of_le_two {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2) : Function.Bijective (φ h1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, φ_surjective h1⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [φ, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hx
  obtain ⟨g, rfl⟩ := hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mul_mem_right _ _ ?_
  have hmem : Polynomial.C (coeff n (cXi n)) * Polynomial.X ^ n ∈ relIdeal n :=
    Ideal.subset_span ⟨n - 1, by dsimp only; rw [Nat.sub_add_cancel h1]⟩
  have hf : (n - 1).factorial = 1 := by
    interval_cases n <;> rfl
  rw [coeff_cXi_self h1, hf] at hmem
  have := Ideal.mul_mem_left _ (Polynomial.C ((-1) ^ (n - 1))) hmem
  rwa [← mul_assoc, ← Polynomial.C_mul, Nat.cast_one, mul_one, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, Polynomial.C_1, one_mul] at this

end Page21

end Folder2
