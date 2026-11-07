module

public import Mathlib
public import Challenge.Upstream.DerivationLeibnizProd

@[expose] public section

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

/-- The relations of `CK`: the components `c^m(ξ^n) ζ^m`, `m ≥ 1`. -/
noncomputable def relIdeal (n : ℕ) : Ideal (Polynomial ℤ) :=
  Ideal.span (Set.range fun m : ℕ =>
    Polynomial.C (coeff (m + 1) (cXi n)) * Polynomial.X ^ (m + 1))

/-- The Chern ring `CK` of `K = K(P^{n−1})` with `L` geometric. -/
abbrev CK (n : ℕ) := Polynomial ℤ ⧸ relIdeal n

/-- The graded ring `GK = ℤ[ζ]/(ζ^n)`. -/
abbrev GK (n : ℕ) := Polynomial ℤ ⧸ Ideal.span {(Polynomial.X : Polynomial ℤ) ^ n}

theorem relIdeal_le {n : ℕ} (hn : 1 ≤ n) :
    relIdeal n ≤ Ideal.span {(Polynomial.X : Polynomial ℤ) ^ n} := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨m, rfl⟩
  rcases lt_or_ge (m + 1) n with h | h
  · simp [coeff_cXi_of_lt hn (by omega) h]
  · exact Ideal.mem_span_singleton.2 (dvd_mul_of_dvd_right (pow_dvd_pow _ h) _)

/-- `φ_K : CK → GK`, `c¹(L) ↦ ζ`. -/
noncomputable def φ {n : ℕ} (hn : 1 ≤ n) : CK n →+* GK n := Ideal.Quotient.factor (relIdeal_le hn)

/-- **Page 21.** For `n ≥ 3`, `φ_K : CK → GK` is surjective and not injective: `ζ^n` is a
nonzero torsion element of `CK`, killed by `(n − 1)!`, while `GK` is torsion-free. -/
theorem φ_not_injective {n : ℕ} (hn : 3 ≤ n) :
    ¬ Function.Injective (φ (by omega : 1 ≤ n)) := by
  sorry

end Page21

end Folder2
