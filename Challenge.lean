module

public import Mathlib

/-!
# The Challenge: one headline statement per folder file

For each file `Grothendieck/FolderNN.lean` of the library, the section below for that folder states
its headline theorem (the one the Lean appendix of the paper presents as the folder's main
verified statement), with `sorry`, together with the definitions its statement depends on, copied
verbatim from the library under the same names. The choices are listed in `CHALLENGE.md`. The
general lemma file `Grothendieck/Upstream/DerivationLeibnizProd.lean`, which `Folder2` needs, is
copied first. This file imports only Mathlib, so that it can be compiled on its own.
-/

-- From Challenge/Upstream/DerivationLeibnizProd.lean
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

end

-- From Challenge/Folder1.lean
@[expose] public section

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section SVD

variable [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- `σ_n^m(T)`, the elementary symmetric function of degree `m` of the first `n` singular
values `s_0(T), …, s_{n-1}(T)` (page 71, (17)). -/
noncomputable def sigma (n m : ℕ) (T : E →ₗ[𝕜] F) : ℝ :=
  ∑ t ∈ (range n).powersetCard m, ∏ i ∈ t, T.singularValues i

end SVD

open scoped ComplexConjugate

end Grothendieck.Folder1

namespace Grothendieck.Folder1

open Finset Module InnerProductSpace Matrix Polynomial

open scoped MatrixOrder ComplexOrder ComplexConjugate

section SigmaSystem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The system (16) of page 71**, for every `m` and `n`, for linear maps between
finite-dimensional complex inner product spaces:
`σ_n^m(u+v) ≤ ∑_{p=0}^{m} σ_n^p(u) σ_n^{m-p}(v)`. -/
theorem sigma_system (u v : E →ₗ[ℂ] F) (n m : ℕ) :
    sigma n m (u + v) ≤ ∑ p ∈ range (m + 1), sigma n p u * sigma n (m - p) v := by
  sorry

end SigmaSystem

end Grothendieck.Folder1

end

-- From Challenge/Folder2.lean
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
    ¬ Function.Injective (φ (Nat.le_trans (Nat.le_add_left 1 2) hn)) := by
  sorry

end Page21

end Folder2

end

-- From Challenge/Folder5.lean
@[expose] public section

namespace Grothendieck.Folder5

open Nat

/-- `qᵢ = (p^{i+1})! / ((p^i)!)^p`. -/
def q (p i : ℕ) : ℕ := (p ^ (i + 1))! / ((p ^ i)!) ^ p

lemma multinomial_spec_pow (p i : ℕ) :
    ((p ^ i)!) ^ p * Nat.multinomial (Finset.range p) (fun _ => p ^ i) = (p ^ (i + 1))! := by
  have h := Nat.multinomial_spec (Finset.range p) (fun _ => p ^ i)
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_const, smul_eq_mul] at h
  rwa [← pow_succ'] at h

/-- `qᵢ` is the multinomial coefficient of `p` blocks of size `p^i`. -/
theorem q_eq_multinomial (p i : ℕ) :
    q p i = Nat.multinomial (Finset.range p) (fun _ => p ^ i) := by
  rw [q, ← multinomial_spec_pow, Nat.mul_div_cancel_left _ (pow_pos (factorial_pos _) _)]

/-- `((p^i)!)^p · qᵢ = (p^{i+1})!`: `qᵢ` is an integer. -/
theorem factorial_eq_mul_q (p i : ℕ) : (p ^ (i + 1))! = ((p ^ i)!) ^ p * q p i := by
  rw [q_eq_multinomial, multinomial_spec_pow]

end Grothendieck.Folder5

namespace Grothendieck.Folder5

open Nat MvPolynomial

/-- Lucas: `C(p^e m, p^e) ≡ m [MOD p]`. -/
theorem choose_pow_mul_pow_modEq (p : ℕ) [hp : Fact p.Prime] (e m : ℕ) :
    choose (p ^ e * m) (p ^ e) ≡ m [MOD p] := by
  induction e with
  | zero => simp [Nat.ModEq]
  | succ e ih =>
    refine (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)).trans ?_
    have h1 : p ^ (e + 1) * m = p * (p ^ e * m) := by ring
    have h2 : p ^ (e + 1) = p * p ^ e := by ring
    have hp0 : 0 < p := hp.out.pos
    rw [h1, h2, Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp0,
      Nat.mul_div_cancel_left _ hp0, choose_zero_right, one_mul]
    exact ih

/-- Every `k ≠ 0` has a power `p^e ≤ k` with `C(k, p^e)` prime to `p` (take `p^e ∥ k`). -/
theorem exists_pow_le_not_dvd_choose (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    ∃ e, p ^ e ≤ k ∧ ¬ p ∣ choose k (p ^ e) := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.out.one_lt.ne'
  refine ⟨e, Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hm)), ?_⟩
  rwa [(choose_pow_mul_pow_modEq p e m).dvd_iff dvd_rfl]

/-- In a divided-power ideal, for `k ≠ 0` there are `p^e ≤ k` and `c` prime to `p` with
`C(k, p^e) γ_k(x) = γ_{p^e}(x) γ_{k − p^e}(x)`, `C(k, p^e)` prime to `p`. -/
theorem dpow_split {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] {I : Ideal R}
    (hI : DividedPowers I) {x : R} (hx : x ∈ I) {k : ℕ} (hk : k ≠ 0) :
    ∃ e, p ^ e ≤ k ∧ ¬ p ∣ choose k (p ^ e) ∧
      (choose k (p ^ e) : R) * hI.dpow k x = hI.dpow (p ^ e) x * hI.dpow (k - p ^ e) x := by
  obtain ⟨e, hle, hnd⟩ := exists_pow_le_not_dvd_choose p hk
  exact ⟨e, hle, hnd, by rw [hI.mul_dpow hx, Nat.add_sub_cancel' hle]⟩

variable (W : Type*) [CommRing W] (p ν : ℕ)

/-- The relations `Λᵢ^p − qᵢΛᵢ₊₁` (`i < ν`) and `Λ_ν^p`. -/
noncomputable def rel : Ideal (MvPolynomial (Fin (ν + 1)) W) :=
  Ideal.span (Set.range (fun i : Fin ν => X i.castSucc ^ p - (q p i : MvPolynomial _ W) * X i.succ)
    ∪ {X (Fin.last ν) ^ p})

/-- `A^{(ν)} = W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p)`. -/
abbrev Aν := MvPolynomial (Fin (ν + 1)) W ⧸ rel W p ν

/-- The class of `Λᵢ`. -/
noncomputable def Lam (i : Fin (ν + 1)) : Aν W p ν := Ideal.Quotient.mk _ (X i)

theorem Lam_pow_castSucc (i : Fin ν) :
    Lam W p ν i.castSucc ^ p = (q p i : Aν W p ν) * Lam W p ν i.succ := by
  rw [Lam, Lam, ← map_pow, ← map_natCast (Ideal.Quotient.mk (rel W p ν)), ← map_mul,
    Ideal.Quotient.eq]
  exact Ideal.subset_span (Or.inl ⟨i, rfl⟩)

theorem Lam_last_pow : Lam W p ν (Fin.last ν) ^ p = 0 := by
  rw [Lam, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Or.inr rfl)

/-- The monomial `Λ^a`, `a` in the box `0 ≤ aᵢ < p`. -/
noncomputable def mono (a : Fin (ν + 1) → Fin p) : Aν W p ν := ∏ i, Lam W p ν i ^ (a i : ℕ)

theorem mono_eq (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) :
    mono W p ν a = Lam W p ν j ^ (a j : ℕ) *
      ∏ i ∈ Finset.univ.erase j, Lam W p ν i ^ (a i : ℕ) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

theorem mono_update (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) (v : Fin p) :
    mono W p ν (Function.update a j v) = Lam W p ν j ^ (v : ℕ) *
      ∏ i ∈ Finset.univ.erase j, Lam W p ν i ^ (a i : ℕ) := by
  rw [mono_eq W p ν _ j, Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The `W`-span of the box monomials. -/
noncomputable def boxSpan : Submodule W (Aν W p ν) := Submodule.span W (Set.range (mono W p ν))

/-- The box monomials are stable under multiplication by each `Λⱼ` (carry in base `p`). -/
theorem Lam_mul_mono_mem (j : Fin (ν + 1)) (a : Fin (ν + 1) → Fin p) :
    Lam W p ν j * mono W p ν a ∈ boxSpan W p ν := by
  induction j using Fin.reverseInduction generalizing a with
  | last =>
    rw [mono_eq W p ν a (Fin.last ν), ← mul_assoc, ← _root_.pow_succ']
    by_cases h : (a (Fin.last ν) : ℕ) + 1 < p
    · rw [show (a (Fin.last ν) : ℕ) + 1 = ((⟨_, h⟩ : Fin p) : ℕ) from rfl,
        ← mono_update]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : (a (Fin.last ν) : ℕ) + 1 = p := by have := (a (Fin.last ν)).2; omega
      rw [this, Lam_last_pow, zero_mul]
      exact Submodule.zero_mem _
  | cast i ih =>
    rw [mono_eq W p ν a i.castSucc, ← mul_assoc, ← _root_.pow_succ']
    by_cases h : (a i.castSucc : ℕ) + 1 < p
    · rw [show (a i.castSucc : ℕ) + 1 = ((⟨_, h⟩ : Fin p) : ℕ) from rfl, ← mono_update]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : (a i.castSucc : ℕ) + 1 = p := by have := (a i.castSucc).2; omega
      have hp : 0 < p := by have := (a i.castSucc).2; omega
      have h0 := mono_update W p ν a i.castSucc ⟨0, hp⟩
      simp only [pow_zero, one_mul] at h0
      rw [this, Lam_pow_castSucc, mul_assoc, ← h0, ← nsmul_eq_mul]
      exact Submodule.smul_of_tower_mem _ _ (ih _)

theorem boxSpan_eq_top (hp : 0 < p) : boxSpan W p ν = ⊤ := by
  have hmul : ∀ x ∈ boxSpan W p ν, ∀ j, x * Lam W p ν j ∈ boxSpan W p ν := by
    intro x hx j
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; rw [mul_comm]; exact Lam_mul_mono_mem W p ν j a
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  have h1 : (1 : Aν W p ν) ∈ boxSpan W p ν := by
    have : mono W p ν (fun _ => ⟨0, hp⟩) = 1 := by simp [mono]
    rw [← this]; exact Submodule.subset_span ⟨_, rfl⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C w =>
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk W, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ w h1
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | mul_X f j hf => rw [map_mul]; exact hmul _ hf j

section Embedding

variable (K : Type*) [Field K] [CharZero K] [Algebra W K]

/-- `B = K[X]/(X^{p^{ν+1}})`, `K` a field of characteristic zero receiving `W`. -/
abbrev Bν := Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ p ^ (ν + 1)}

/-- The class of `X` in `B`. -/
noncomputable def xb : Bν p ν K := Ideal.Quotient.mk _ Polynomial.X

omit [CharZero K] in
theorem xb_pow_eq_zero {n : ℕ} (hn : p ^ (ν + 1) ≤ n) : xb p ν K ^ n = 0 := by
  rw [xb, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ hn

/-- `cᵢ = 1/(p^i)!`. -/
noncomputable def cf (i : ℕ) : K := (((p ^ i)! : ℕ) : K)⁻¹

theorem cf_pow (i : ℕ) : cf p K i ^ p = (q p i : K) * cf p K (i + 1) := by
  have h := congrArg (fun n : ℕ => (n : K)) (factorial_eq_mul_q p i)
  simp only [Nat.cast_mul, Nat.cast_pow] at h
  have h2 : (((p ^ (i + 1))! : ℕ) : K) ≠ 0 := by exact_mod_cast (factorial_ne_zero _)
  have h3 : (q p i : K) ≠ 0 := fun h0 => h2 (by rw [h, h0, mul_zero])
  rw [cf, cf, inv_pow, h]
  field_simp

/-- `ψ₀ : Λᵢ ↦ X^{p^i}/(p^i)!`. -/
noncomputable def psi0 : MvPolynomial (Fin (ν + 1)) W →ₐ[W] Bν p ν K :=
  MvPolynomial.aeval (R := W) (S₁ := Bν p ν K) fun i : Fin (ν + 1) =>
    (algebraMap (K) (Bν p ν K) (cf p K (i : ℕ)) : Bν p ν K) * xb p ν K ^ (p ^ (i : ℕ))

theorem rel_le_ker : rel W p ν ≤ RingHom.ker (psi0 W p ν K) := by
  rw [rel, Ideal.span_le]
  rintro _ (⟨i, rfl⟩ | rfl)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast,
      psi0, aeval_X, Fin.val_castSucc, Fin.val_succ]
    rw [mul_pow, ← pow_mul, ← _root_.pow_succ, ← map_pow, cf_pow, map_mul, map_natCast]
    ring
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_pow, psi0, aeval_X, Fin.val_last]
    rw [mul_pow, ← pow_mul, ← _root_.pow_succ, xb_pow_eq_zero p ν K le_rfl, mul_zero]

/-- `ψ : A^{(ν)} → K[X]/(X^{p^{ν+1}})`. -/
noncomputable def psi : Aν W p ν →ₐ[W] Bν p ν K :=
  Ideal.Quotient.liftₐ (rel W p ν) (psi0 W p ν K) fun _ ha => RingHom.mem_ker.mp (rel_le_ker W p ν K ha)

theorem psi_Lam (i : Fin (ν + 1)) :
    psi W p ν K (Lam W p ν i) =
      algebraMap (K) (Bν p ν K) (cf p K i) * xb p ν K ^ (p ^ (i : ℕ)) := by
  change psi0 W p ν K (X i) = _
  simp [psi0]

theorem psi_Lam_zero : psi W p ν K (Lam W p ν 0) = xb p ν K := by
  rw [psi_Lam, Fin.val_zero, pow_zero, pow_one, cf, pow_zero, factorial_one, Nat.cast_one,
    inv_one, map_one, one_mul]

/-- The degree `Σ aᵢ p^i` of a box monomial. -/
def deg {m : ℕ} (a : Fin m → Fin p) : ℕ := ∑ i, (a i : ℕ) * p ^ (i : ℕ)

theorem deg_lt {m : ℕ} (a : Fin m → Fin p) : deg p a < p ^ m := by
  induction m with
  | zero => simp [deg]
  | succ m ih =>
    have := ih (fun i => a i.succ)
    have h0 := (a 0).2
    simp only [deg, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      _root_.pow_succ] at this ⊢
    have : ∑ i : Fin m, (a i.succ : ℕ) * (p ^ (i : ℕ) * p) =
        p * ∑ i : Fin m, (a i.succ : ℕ) * p ^ (i : ℕ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    nlinarith

theorem deg_injective {m : ℕ} : Function.Injective (deg p (m := m)) := by
  induction m with
  | zero => intro a b _; funext i; exact i.elim0
  | succ m ih =>
    intro a b h
    have key : ∀ c : Fin (m + 1) → Fin p,
        deg p c = (c 0 : ℕ) + p * deg p (fun i => c i.succ) := by
      intro c
      simp only [deg, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
        _root_.pow_succ, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    rw [key a, key b] at h
    have ha := (a 0).2
    have hb := (b 0).2
    have h0 : (a 0 : ℕ) = b 0 := by
      have := congrArg (· % p) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    have hp : 0 < p := by omega
    have h1 : deg p (fun i => a i.succ) = deg p (fun i => b i.succ) := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hp (by omega)
    have := ih h1
    funext i
    refine Fin.cases (Fin.ext h0) (fun j => congrFun this j) i

omit [CharZero K] in
theorem algebraMap_Bν (k : K) :
    algebraMap K (Bν p ν K) k = Ideal.Quotient.mk _ (Polynomial.C k) := rfl

theorem psi_mono (a : Fin (ν + 1) → Fin p) :
    psi W p ν K (mono W p ν a) =
      algebraMap K (Bν p ν K) (∏ i : Fin (ν + 1), cf p K (i : ℕ) ^ (a i : ℕ)) * xb p ν K ^ deg p a := by
  simp only [mono, map_prod, map_pow, psi_Lam, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, deg]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem cf_ne_zero (i : ℕ) : cf p K i ≠ 0 := by
  rw [cf]; exact inv_ne_zero (by exact_mod_cast factorial_ne_zero _)

/-- **`ψ` is injective**: the box monomials `Λ^a` span `A^{(ν)}` and go to nonzero multiples of
the distinct powers `X^{Σ aᵢ p^i}`, `Σ aᵢ p^i < p^{ν+1}`. -/
theorem psi_injective (hinj : Function.Injective (algebraMap W K)) (hp : 0 < p) :
    Function.Injective (psi W p ν K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : x ∈ boxSpan W p ν := by rw [boxSpan_eq_top W p ν hp]; trivial
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun W).mp hx'
  set P : Polynomial K := ∑ a, Polynomial.C (algebraMap W K (w a) * ∏ i : Fin (ν + 1), cf p K (i : ℕ) ^ (a i : ℕ)) *
    Polynomial.X ^ deg p a with hP
  have hmk : Ideal.Quotient.mk _ P = psi W p ν K (∑ a, w a • mono W p ν a) := by
    simp only [hP, map_sum, map_mul, map_smul, psi_mono, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (w a), Algebra.smul_def (R := K) (A := Bν p ν K), xb,
      algebraMap_Bν, algebraMap_Bν]
    ring
  rw [hx, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
    at hmk
  have hw : ∀ b, w b = 0 := by
    intro b
    have h := hmk (deg p b) (deg_lt p b)
    rw [hP, Polynomial.finsetSum_coeff] at h
    simp only [Polynomial.coeff_C_mul_X_pow] at h
    rw [Finset.sum_eq_single b (fun a _ hab => ite_eq_right_iff.mpr fun h' =>
      absurd (deg_injective p h').symm hab) (by simp)] at h
    simp only [ite_true] at h
    have := (mul_eq_zero.mp h).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (cf_ne_zero p K (i : ℕ)))
    exact hinj (by rw [this, map_zero])
  simp [hw]

end Embedding

section DividedPowers

/-- The ideal `(Λ₀, …, Λ_ν)` of `A^{(ν)}`. -/
noncomputable def Ibar : Ideal (Aν W p ν) := Ideal.span (Set.range (Lam W p ν))

theorem Lam_mem_Ibar (i : Fin (ν + 1)) : Lam W p ν i ∈ Ibar W p ν :=
  Ideal.subset_span ⟨i, rfl⟩

variable (K : Type*) [Field K] [CharZero K] [Algebra W K]

theorem inverse_factorial_Bν (n : ℕ) :
    Ring.inverse ((n ! : ℕ) : Bν p ν K) = algebraMap K (Bν p ν K) ((n ! : K)⁻¹) := by
  have hu : IsUnit ((n ! : ℕ) : Bν p ν K) := by
    rw [← map_natCast (algebraMap K (Bν p ν K))]
    exact (IsUnit.mk0 _ (by exact_mod_cast factorial_ne_zero n)).map _
  have h1 : ((n ! : ℕ) : Bν p ν K) * algebraMap K (Bν p ν K) ((n ! : K)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap K (Bν p ν K)), ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast factorial_ne_zero n), map_one]
  calc Ring.inverse ((n ! : ℕ) : Bν p ν K)
      = Ring.inverse ((n ! : ℕ) : Bν p ν K) *
          (((n ! : ℕ) : Bν p ν K) * algebraMap K (Bν p ν K) ((n ! : K)⁻¹)) := by
        rw [h1, mul_one]
    _ = _ := Ring.inverse_mul_cancel_left _ _ hu

open Classical in
/-- The divided powers `x^n/n!` on an ideal of the `ℚ`-algebra `B`. -/
noncomputable abbrev ratDP (J : Ideal (Bν p ν K)) : DividedPowers J :=
  DividedPowers.RatAlgebra.dividedPowers J

theorem ratDP_xb {J : Ideal (Bν p ν K)} (hx : xb p ν K ∈ J) (i : ℕ) :
    (ratDP p ν K J).dpow (p ^ i) (xb p ν K) =
      algebraMap K (Bν p ν K) (cf p K i) * xb p ν K ^ (p ^ i) := by
  rw [DividedPowers.RatAlgebra.dpow_apply, ite_eq_left hx, inverse_factorial_Bν, cf]

theorem ratDP_xb_eq_zero {J : Ideal (Bν p ν K)} (hx : xb p ν K ∈ J) {k : ℕ}
    (hk : p ^ (ν + 1) ≤ k) : (ratDP p ν K J).dpow k (xb p ν K) = 0 := by
  rw [DividedPowers.RatAlgebra.dpow_apply, ite_eq_left hx, xb_pow_eq_zero p ν K hk, mul_zero]

theorem xb_mem_map : xb p ν K ∈ (Ibar W p ν).map (psi W p ν K) := by
  simpa [psi_Lam_zero] using Ideal.mem_map_of_mem (psi W p ν K) (Lam_mem_Ibar W p ν 0)

theorem psi_Lam_eq_dpow (i : Fin (ν + 1)) :
    psi W p ν K (Lam W p ν i) =
      (ratDP p ν K ((Ibar W p ν).map (psi W p ν K))).dpow (p ^ (i : ℕ)) (xb p ν K) := by
  rw [ratDP_xb p ν K (xb_mem_map W p ν K), psi_Lam]

variable [Fact p.Prime]

/-- Every `γ_k(X)` of `B` comes from `A^{(ν)}`, from `(Λ)` if `k ≠ 0` (induction on `k`). -/
theorem exists_psi_eq_dpow_xb (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (k : ℕ) :
    ∃ z : Aν W p ν, (k ≠ 0 → z ∈ Ibar W p ν) ∧
      psi W p ν K z = (ratDP p ν K ((Ibar W p ν).map (psi W p ν K))).dpow k (xb p ν K) := by
  set hJ := ratDP p ν K ((Ibar W p ν).map (psi W p ν K))
  have hx := xb_mem_map W p ν K
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k = 0
    · exact ⟨1, fun h => absurd hk h, by rw [hk, hJ.dpow_zero hx, map_one]⟩
    obtain ⟨e, hle, hc, heq⟩ := dpow_split p hJ hx hk
    by_cases he : e ≤ ν
    · have hlt : k - p ^ e < k := Nat.sub_lt (Nat.pos_of_ne_zero hk)
        (pow_pos (Fact.out : p.Prime).pos _)
      obtain ⟨z', -, hz'⟩ := ih _ hlt
      obtain ⟨v, hv⟩ := hW _ hc
      refine ⟨algebraMap W _ ↑v⁻¹ * (Lam W p ν ⟨e, by omega⟩ * z'),
        fun _ => Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Lam_mem_Ibar W p ν _)), ?_⟩
      rw [map_mul, map_mul, AlgHom.commutes, psi_Lam_eq_dpow, hz']
      change _ * (hJ.dpow (p ^ e) _ * _) = _
      rw [← heq, ← map_natCast (algebraMap W (Bν p ν K)), ← hv, ← mul_assoc, ← map_mul,
        Units.inv_mul, map_one, one_mul]
    · refine ⟨0, fun _ => Ideal.zero_mem _, ?_⟩
      rw [map_zero, ratDP_xb_eq_zero p ν K hx]
      exact le_trans (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)) hle

theorem psi_hmem (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (n : ℕ) {x : Aν W p ν}
    (hx : x ∈ Ibar W p ν) : ∃ (y : Aν W p ν) (_ : n ≠ 0 → y ∈ Ibar W p ν),
      (psi W p ν K : Aν W p ν →+* Bν p ν K) y =
        (ratDP p ν K ((Ibar W p ν).map (psi W p ν K))).dpow n
          ((psi W p ν K : Aν W p ν →+* Bν p ν K) x) := by
  set hJ := ratDP p ν K ((Ibar W p ν).map (psi W p ν K))
  have hmap : ∀ y ∈ Ibar W p ν, psi W p ν K y ∈ (Ibar W p ν).map (psi W p ν K) :=
    fun y hy => Ideal.mem_map_of_mem _ hy
  simp only [RingHom.coe_coe]
  induction hx using Submodule.span_induction generalizing n with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨z, hz, hz'⟩ := exists_psi_eq_dpow_xb W p ν K hW (n * p ^ (i : ℕ))
    refine ⟨(uniformBell n (p ^ (i : ℕ)) : Aν W p ν) * z, fun hn => Ideal.mul_mem_left _ _
      (hz (Nat.mul_ne_zero hn (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))), ?_⟩
    rw [psi_Lam_eq_dpow, hJ.dpow_comp (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (xb_mem_map W p ν K), map_mul, map_natCast, hz']
  | zero =>
    by_cases hn : n = 0
    · exact ⟨1, fun h => absurd hn h, by rw [map_zero, hn, hJ.dpow_zero (Ideal.zero_mem _),
        map_one]⟩
    · exact ⟨0, fun _ => Ideal.zero_mem _, by rw [map_zero, hJ.dpow_eval_zero hn]⟩
  | add x y hx hy ihx ihy =>
    choose fx hfx hfx' using ihx
    choose fy hfy hfy' using ihy
    refine ⟨∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, fx kl.1 * fy kl.2, fun hn => ?_, ?_⟩
    · refine Ideal.sum_mem _ fun kl hkl => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      by_cases h1 : kl.1 = 0
      · exact Ideal.mul_mem_left _ _ (hfy _ (by omega))
      · exact Ideal.mul_mem_right _ _ (hfx _ h1)
    · rw [map_add, hJ.dpow_add (hmap x hx) (hmap y hy), map_sum]
      exact Finset.sum_congr rfl fun kl _ => by rw [map_mul, hfx', hfy']
  | smul a x hx ihx =>
    obtain ⟨z, hz, hz'⟩ := ihx n
    refine ⟨a ^ n * z, fun hn => Ideal.mul_mem_left _ _ (hz hn), ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, map_pow, hz', hJ.dpow_mul (hmap x hx)]

end DividedPowers

section Universal

variable [IsDomain W] [CharZero W] [Fact p.Prime]

/-- **The divided powers on `(Λ₀, …, Λ_ν) ⊂ A^{(ν)}`**, transported from `X^n/n!` along the
injective `ψ : A^{(ν)} → K[X]/(X^{p^{ν+1}})`, `K = Frac W`. -/
noncomputable def dpIbar (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) : DividedPowers (Ibar W p ν) :=
  DividedPowers.ofInjective (Ibar W p ν) ((Ibar W p ν).map (psi W p ν (FractionRing W)))
    (psi W p ν (FractionRing W) : Aν W p ν →+* Bν p ν (FractionRing W))
    (psi_injective W p ν _ (IsFractionRing.injective W _) (Fact.out : p.Prime).pos)
    (ratDP p ν _ _) rfl (psi_hmem W p ν _ hW)

variable (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem rel_le_ker_constantCoeff (hp : p ≠ 0) :
    rel W p ν ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin (ν + 1)) W →+* W) := by
  rw [rel, Ideal.span_le]
  rintro _ (⟨i, rfl⟩ | rfl) <;> simp [zero_pow hp]

/-- The augmentation `ε : A^{(ν)} → W`, `Λᵢ ↦ 0`. -/
noncomputable def eps : Aν W p ν →+* W :=
  Ideal.Quotient.lift (rel W p ν) constantCoeff fun _ ha =>
    RingHom.mem_ker.mp (rel_le_ker_constantCoeff W p ν (Fact.out : p.Prime).ne_zero ha)

omit [IsDomain W] [CharZero W] in
theorem Ibar_le_ker_eps : Ibar W p ν ≤ RingHom.ker (eps W p ν) := by
  rw [Ibar, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp [eps, Lam]

omit [IsDomain W] [CharZero W] in
theorem mem_Ibar_of_eps {x : Aν W p ν} (hx : eps W p ν x = 0) : x ∈ Ibar W p ν := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hf : constantCoeff f = 0 := hx
  have : f ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin (ν + 1)) W)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff, ← constantCoeff_eq, hf] at hm
      exact hm rfl
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ _, hi⟩
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (rel W p ν)) this
  rwa [Ideal.map_span, Set.image_image, Set.image_univ] at h2

/-- The ideal `(Λ₀ − p)`. -/
noncomputable def Kp : Ideal (Aν W p ν) := Ideal.span {Lam W p ν 0 - (p : Aν W p ν)}

/-- `(Λ₀ − p) ∩ (Λ) = (Λ₀ − p)(Λ)` is a sub-divided-power ideal. -/
theorem isSubDPIdeal_Kp : (dpIbar W p ν hW).IsSubDPIdeal (Kp W p ν ⊓ Ibar W p ν) where
  isSubideal := inf_le_right
  dpow_mem n hn j hj := by
    obtain ⟨hjK, hjI⟩ := hj
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hjK
    have ha : a ∈ Ibar W p ν := by
      apply mem_Ibar_of_eps
      have h := Ibar_le_ker_eps W p ν hjI
      rw [RingHom.mem_ker, map_mul, map_sub, map_natCast] at h
      have h0 : eps W p ν (Lam W p ν 0) = 0 := RingHom.mem_ker.mp
        (Ibar_le_ker_eps W p ν (Lam_mem_Ibar W p ν 0))
      rw [h0, zero_sub, mul_neg, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_right (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    refine ⟨?_, (dpIbar W p ν hW).dpow_mem hn hjI⟩
    rw [mul_comm, (dpIbar W p ν hW).dpow_mul ha, ← Nat.sub_add_cancel (Nat.pos_of_ne_zero hn),
      pow_succ, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/-- **`W^{(ν)} = A^{(ν)}/(Λ₀ − p) = W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p, Λ₀ − p)`.** -/
abbrev Wν := Aν W p ν ⧸ Kp W p ν

/-- **The divided powers on `J = (Λ₀, …, Λ_ν) ⊂ W^{(ν)}`**, induced by those of `A^{(ν)}`. -/
noncomputable def dpWν : DividedPowers ((Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν))) :=
  DividedPowers.Quotient.dividedPowers (dpIbar W p ν hW) (isSubDPIdeal_Kp W p ν hW)

include hW in
/-- **Universality (page 4).** `W^{(ν)}`, with the divided powers `dpWν` on `J = (Λ₀, …, Λ_ν)`,
is initial among `W`-algebras `T` with a divided-power ideal `(I, γ)` such that `p ∈ I` and
`γ_n(p) = 0` for `n ≥ p^{ν+1}`: there is exactly one `W`-algebra map `W^{(ν)} → T` compatible
with the divided powers. -/
theorem universal {T : Type*} [CommRing T] [Algebra W T] {I : Ideal T} (hI : DividedPowers I)
    (hpI : (p : T) ∈ I) (hnil : ∀ n, p ^ (ν + 1) ≤ n → hI.dpow n (p : T) = 0) :
    ∃! f : Wν W p ν →ₐ[W] T,
      DividedPowers.IsDPMorphism (dpWν W p ν hW) hI (f : Wν W p ν →+* T) := by
  sorry

end Universal

end Grothendieck.Folder5

end

-- From Challenge/Folder10.lean
@[expose] public section

namespace Grothendieck.Folder10.NormOneTorus

open CategoryTheory groupCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (χ : Γ →* ℤˣ) (M : Rep.{0} k Γ)

/-- `M` twisted by the sign `χ`: `g ⋆ x = χ(g) · g x`. For `M = Lˣ` this is the norm-one torus
`G = Ker(N : R_{Z/k} 𝔾_m → 𝔾_m)` on `L`-points, `g ⋆ x = g(x)^{χ g}`. -/
def twistRep : Representation k Γ M.V where
  toFun g := (χ g : ℤ) • M.ρ g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

/-- The identity of `M × M` when `χ g = 1`, the swap of the two factors otherwise. -/
def swapLin (g : Γ) : M.V × M.V →ₗ[k] M.V × M.V :=
  if χ g = 1 then LinearMap.id else (LinearMap.snd k M.V M.V).prod (LinearMap.fst k M.V M.V)

lemma swapLin_apply (g : Γ) (v : M.V × M.V) :
    swapLin χ M g v = if χ g = 1 then v else (v.2, v.1) := by
  unfold swapLin; split_ifs <;> rfl

/-- `M × M` with `g · (x, y) = (g x, g y)` if `χ g = 1` and `(g y, g x)` otherwise: for
`M = Lˣ` and `χ` the sign of a quadratic `Z ⊆ L`, this is `(Z ⊗_k L)ˣ`, the `L`-points of
`R_{Z/k} 𝔾_m`, written in the basis of the two idempotents. -/
def indRep : Representation k Γ (M.V × M.V) where
  toFun g := ((M.ρ g).prodMap (M.ρ g)) ∘ₗ swapLin χ M g
  map_one' := by
    ext v <;> simp [swapLin_apply]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, swapLin_apply, map_mul, Module.End.mul_apply]
    rcases Int.units_eq_one_or (χ g) with hg | hg <;>
      rcases Int.units_eq_one_or (χ h) with hh | hh <;> simp [hg, hh]

lemma indRep_apply (g : Γ) (v : M.V × M.V) :
    indRep χ M g v = if χ g = 1 then (M.ρ g v.1, M.ρ g v.2) else (M.ρ g v.2, M.ρ g v.1) := by
  change (M.ρ g).prodMap (M.ρ g) (swapLin χ M g v) = _
  rw [swapLin_apply]; split_ifs <;> rfl

lemma twistRep_apply (g : Γ) (v : M.V) : twistRep χ M g v = (χ g : ℤ) • M.ρ g v := rfl

/-- `x ↦ (x, -x)`. -/
def torusIncl : (twistRep χ M).IntertwiningMap (indRep χ M) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (twistRep χ M) (indRep χ M)
    (LinearMap.id.prod (-LinearMap.id))
    fun g v => by
      rw [indRep_apply, twistRep_apply]
      rcases Int.units_eq_one_or (χ g) with hg | hg <;> simp [hg]

/-- `(x, y) ↦ x + y`. -/
def normMap : (indRep χ M).IntertwiningMap M.ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (indRep χ M) M.ρ
    (LinearMap.coprod LinearMap.id LinearMap.id)
    fun g v => by
      rw [indRep_apply]
      split_ifs <;> simp [add_comm]

lemma torusIncl_apply (v : M.V) : torusIncl χ M v = (v, -v) := rfl

lemma normMap_apply (v : M.V × M.V) : normMap χ M v = v.1 + v.2 := rfl

/-- `0 → G → Z^* → 𝔾_m → 0` of page 65, at the level of `Γ`-modules. -/
def torusSeq : ShortComplex (Rep.{0} k Γ) where
  X₁ := Rep.of (twistRep χ M)
  X₂ := Rep.of (indRep χ M)
  X₃ := M
  f := Rep.ofHom (torusIncl χ M)
  g := Rep.ofHom (normMap χ M)
  zero := by
    ext v
    simp [torusIncl_apply, normMap_apply]

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Page 65, Exemple 1, at a finite level: by Hilbert 90 (`H1ofAutOnUnitsUnique`),
`H²(Gal(L/K), G(L)) → H²(Gal(L/K), (Z ⊗_K L)ˣ)` is injective, for every sign `χ`. -/
theorem norm_one_torus_H2_injective (χ : Gal(L/K) →* ℤˣ) :
    Function.Injective
      (map (MonoidHom.id _) (A := Rep.of (twistRep χ (Rep.ofAlgebraAutOnUnits K L)))
        (torusSeq χ (Rep.ofAlgebraAutOnUnits K L)).f 2).hom := by
  sorry

end Grothendieck.Folder10.NormOneTorus

end

-- From Challenge/Folder11.lean
@[expose] public section

namespace Folder11.Simplicial

open TensorProduct

universe u

variable {k : Type u} [Field k]

/-- A Poincaré algebra: finite-dimensional, with `(x, y) ↦ κ(xy)` non-degenerate. -/
def IsPoincare (A : Type*) [CommRing A] [Algebra k A] (κ : A →ₗ[k] k) : Prop :=
  FiniteDimensional k A ∧ ∀ x : A, (∀ y, κ (y * x) = 0) → x = 0

/-- A contravariant functor from finite non-empty sets (all maps) to gauged commutative
`k`-algebras with morphisms `(f_*, f^*)` (page 33): for `α : I → J`, the pull-back
`A(I) → A(J)` is an algebra map, the push-forward `A(J) → A(I)` satisfies the projection
formula and preserves the gauges. -/
structure SFun (k : Type u) [Field k] where
  obj : ℕ → Type u
  [ring : ∀ n, CommRing (obj n)]
  [alg : ∀ n, Algebra k (obj n)]
  κ : ∀ n, obj n →ₗ[k] k
  pull : ∀ {m n : ℕ}, (Fin (m + 1) → Fin (n + 1)) → obj m →ₐ[k] obj n
  push : ∀ {m n : ℕ}, (Fin (m + 1) → Fin (n + 1)) → obj n →ₗ[k] obj m
  pull_id : ∀ n, pull (id : Fin (n + 1) → Fin (n + 1)) = AlgHom.id k (obj n)
  pull_comp : ∀ {l m n : ℕ} (α : Fin (l + 1) → Fin (m + 1)) (β : Fin (m + 1) → Fin (n + 1)),
    pull (β ∘ α) = (pull β).comp (pull α)
  push_id : ∀ n, push (id : Fin (n + 1) → Fin (n + 1)) = LinearMap.id
  push_comp : ∀ {l m n : ℕ} (α : Fin (l + 1) → Fin (m + 1)) (β : Fin (m + 1) → Fin (n + 1)),
    push (β ∘ α) = push α ∘ₗ push β
  proj : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)) (y : obj m) (x : obj n),
    push α (pull α y * x) = y * push α x
  gauge : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)) (x : obj n), κ m (push α x) = κ n x

attribute [instance] SFun.ring SFun.alg

namespace SFun

variable (A : SFun k)

/-- The Künneth map `A(I) ⊗ A(pt) → A(I ⊔ pt)` given by the two pull-backs. -/
noncomputable def kun (n : ℕ) : A.obj n ⊗[k] A.obj 0 →ₐ[k] A.obj (n + 1) :=
  Algebra.TensorProduct.productMap (A.pull (Fin.castSucc : Fin (n + 1) → Fin (n + 2)))
    (A.pull (m := 0) fun _ => Fin.last (n + 1))

end SFun

/-- A special simplicial algebra (pages 37 and 41, with the edition's precisions): `A(pt)` is
Poincaré, the Künneth maps `A(I) ⊗ A(pt) → A(I ⊔ pt)` are isomorphisms and the gauges are
multiplicative. -/
structure Special (A : SFun k) : Prop where
  poincare : IsPoincare (A.obj 0) (A.κ 0)
  kunneth : ∀ n, Function.Bijective (A.kun n)
  gauge_mul : ∀ n a b, A.κ (n + 1) (A.kun n (a ⊗ₜ b)) = A.κ n a * A.κ 0 b

/-- A morphism of `𝒞` between two gauged algebras (page 33): an algebra map `f^*` backwards and
an additive `f_*` forwards, with the projection formula and `κ_B f_* = κ_A`. -/
structure GHom (A B : Type*) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (κA : A →ₗ[k] k) (κB : B →ₗ[k] k) where
  push : A →ₗ[k] B
  pull : B →ₐ[k] A
  proj : ∀ y x, push (pull y * x) = y * push x
  gauge : ∀ x, κB (push x) = κA x

/-- A natural transformation `A → B` of simplicial bivariant algebras: a morphism of `𝒞` at each
`I`, natural for pull-backs and push-forwards. -/
structure NatT (A B : SFun k) where
  push : ∀ n, A.obj n →ₗ[k] B.obj n
  pull : ∀ n, B.obj n →ₐ[k] A.obj n
  proj : ∀ n y x, push n (pull n y * x) = y * push n x
  gauge : ∀ n x, B.κ n (push n x) = A.κ n x
  nat_pull : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)),
    (pull n).comp (B.pull α) = (A.pull α).comp (pull m)
  nat_push : ∀ {m n : ℕ} (α : Fin (m + 1) → Fin (n + 1)),
    B.push α ∘ₗ push n = push m ∘ₗ A.push α

/-- **Pages 37 and 41, in the edition's precise form (commutative case).** Evaluation at a
point, from special simplicial bivariant algebras to Poincaré algebras, is faithful, full and
essentially surjective, hence an equivalence. -/
theorem evaluation_equivalence :
    (∀ {A B : SFun k}, Special B → ∀ φ ψ : NatT A B, φ.pull 0 = ψ.pull 0 →
      ∀ n, φ.pull n = ψ.pull n ∧ φ.push n = ψ.push n) ∧
    (∀ {A B : SFun k}, Special B → ∀ g : GHom (A.obj 0) (B.obj 0) (A.κ 0) (B.κ 0),
      ∃ φ : NatT A B, φ.pull 0 = g.pull ∧ φ.push 0 = g.push) ∧
    (∀ (P : Type u) [CommRing P] [Algebra k P] (κ : P →ₗ[k] k), IsPoincare P κ →
      ∃ (A : SFun k) (_ : Special A) (e : P ≃ₐ[k] A.obj 0), ∀ x, A.κ 0 (e x) = κ x) := by
  sorry

end Folder11.Simplicial

end

-- From Challenge/Folder13.lean
@[expose] public section

open Complex Polynomial

open scoped Pointwise

namespace Grothendieck.Folder13

/-- **Grothendieck, page 47, the Tate case** (« c'est une puissance de Tate, et ça marche »;
forme reconstituée par l'édition). For the Tate motive `ℚ(n)`, the rational numbers lying in
the de Rham line `(2πi)ⁿ ℚ̄` are all of `ℚ` when `n = 0` and only `0` otherwise, which is
`V^G` for the weight-`n` character of `𝔾_m`. Assumes the transcendence of `π` (Lindemann),
not in Mathlib. -/
theorem tate (hπ : Transcendental ℚ (Real.pi : ℂ)) (n : ℤ) :
    {q : ℚ | ∃ α : ℂ, IsAlgebraic ℚ α ∧ (q : ℂ) = (2 * Real.pi * I) ^ n * α} =
      if n = 0 then Set.univ else {0} := by
  sorry

end Grothendieck.Folder13

end

-- From Challenge/Folder16.lean
@[expose] public section

namespace Grothendieck.Folder16

open LieModule

section Projecteurs

variable {E : Type*} [Ring E]

/-- `x` is homogeneous of degree `d` for the grading given by the idempotents `π`:
`π_b x π_a = 0` unless `b = a + d`. -/
def Homogene (π : ℤ → E) (d : ℤ) (x : E) : Prop :=
  ∀ a b, b ≠ a + d → π b * x * π a = 0

/-- The grading data: `π` orthogonal idempotents of sum `1`, zero outside `[0, 2n]`. -/
structure Graduation (π : ℤ → E) (n : ℕ) : Prop where
  idem : ∀ a, π a * π a = π a
  orth : ∀ a b, a ≠ b → π a * π b = 0
  supp : ∀ a, a ∉ Finset.Icc (0 : ℤ) (2 * n) → π a = 0
  sum : ∑ a ∈ Finset.Icc (0 : ℤ) (2 * n), π a = 1

variable {π : ℤ → E} {n : ℕ}

end Projecteurs

section DecompositionPrimitive

variable {E : Type*} [Ring E] {π : ℤ → E} {n : ℕ}

/-- The primitive decomposition `M^a = ⊕ L^β P^j` (`j + 2β = a`), read in the ring `E`:
orthogonal idempotents `p j β` of sum `1`, `p j β` living in degree `j + 2β`, `L` carrying
the block `(j, β)` to `(j, β + 1)` and killing the top `(j, n - j)` of each chain, and the
image of `p j β` contained in `L^β` times the image of `p j 0` (`L^β P^j`, not merely a
complement). -/
structure DecompositionPrimitive (π : ℤ → E) (n : ℕ) (L : E) (p : ℕ → ℕ → E) : Prop where
  idem : ∀ j ≤ n, ∀ β ≤ n - j, p j β * p j β = p j β
  orth : ∀ j ≤ n, ∀ β ≤ n - j, ∀ k ≤ n, ∀ γ ≤ n - k, (j, β) ≠ (k, γ) → p j β * p k γ = 0
  sum : ∑ j ∈ Finset.range (n + 1), ∑ β ∈ Finset.range (n - j + 1), p j β = 1
  left : ∀ j ≤ n, ∀ β ≤ n - j, ∀ a : ℤ,
    π a * p j β = if a = (j : ℤ) + 2 * β then p j β else 0
  right : ∀ j ≤ n, ∀ β ≤ n - j, ∀ a : ℤ,
    p j β * π a = if a = (j : ℤ) + 2 * β then p j β else 0
  comm : ∀ j ≤ n, ∀ β < n - j, L * p j β = p j (β + 1) * L
  top : ∀ j ≤ n, L * p j (n - j) = 0
  image : ∀ j ≤ n, ∀ β ≤ n - j, ∃ y, p j β = L ^ β * p j 0 * y

/-- **Pages 4–12, the criterion of no. 6, (1) ⇒ (2) and (3), over `ℤ` and with no module**
(finding `16-graded-ring-lefschetz-criterion`). In a ring `E` graded by orthogonal idempotents
`π_a` (`a ∈ [0, 2n]`), let `ℰ` be a subring containing `L` of degree `2` and one-sided inverses
`wᵢ` of `L^{n-i}` (`(6.3)ᵢ`), and let `p` be the primitive decomposition, read in `E`. Then the
grading projectors, every primitive projector and the pseudo-inverse `Λ` lie in `ℰ`; `Λ` has
degree `-2` and satisfies `(6.7)`. -/
theorem critere_lefschetz (ℰ : Subring E) (G : Graduation π n) {L : E} (hLE : L ∈ ℰ)
    (hL : Homogene π 2 L) {w : ℕ → E} (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i))
    {p : ℕ → ℕ → E} (D : DecompositionPrimitive π n L p) :
    (∀ a, π a ∈ ℰ) ∧ (∀ j ≤ n, ∀ β ≤ n - j, p j β ∈ ℰ) ∧
      ∃ Λ ∈ ℰ, Homogene π (-2) Λ ∧
        L * Λ = 1 - ∑ j ∈ Finset.range (n + 1), p j 0 ∧
        Λ * L = 1 - ∑ j ∈ Finset.range (n + 1), p j (n - j) := by
  sorry

end DecompositionPrimitive

end Grothendieck.Folder16

end

-- From Challenge/Folder19.lean
@[expose] public section

namespace Grothendieck.Folder19

open CategoryTheory Limits

universe w v u₁ u₂

section ContreExemple

/-- An object `(X, Y)` of `Bool → Type`: `X` at `true`, `Y` at `false`. -/
def mkObj (X Y : Type) : Bool → Type
  | true => X
  | false => Y

/-- Pairs `(X, Y)` with `Y → Nonempty X`: if `Y` is inhabited, so is `X`. -/
def P : ObjectProperty (Bool → Type) := fun Z => Z false → Nonempty (Z true)

/-- The coreflection `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def Robj (Z : Bool → Type) : P.FullSubcategory :=
  ⟨mkObj (Z true) {_y : Z false // Nonempty (Z true)}, fun y => y.2⟩

/-- The hom-set bijection of the coreflection. -/
def e (X : P.FullSubcategory) (Z : Bool → Type) : (P.ι.obj X ⟶ Z) ≃ (X ⟶ Robj Z) where
  toFun φ := P.homMk fun b => match b with
    | true => φ true
    | false => TypeCat.ofHom fun q => ⟨φ false q, (X.property q).map (φ true)⟩
  invFun ψ := fun b => match b with
    | true => ψ.hom true
    | false => ψ.hom false ≫ TypeCat.ofHom Subtype.val
  left_inv φ := by
    funext b; cases b <;> rfl
  right_inv ψ := by
    apply ObjectProperty.hom_ext; funext b; cases b <;> rfl

/-- `P ↪ (Bool → Type)` is left adjoint to `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def adjP : P.ι ⊣ Adjunction.rightAdjointOfEquiv e (by
    intro X' X Y f g; apply ObjectProperty.hom_ext; funext b; cases b <;> rfl) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The inclusion of `P` is coreflective. -/
instance : Coreflective P.ι where
  R := _
  adj := adjP

end ContreExemple

section BaseProduit

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂} [∀ i, Category.{v} (B i)]

variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- (3.4) The right adjoint over the product base, `g((Xᵢ)) = ∏ᵢ gᵢ(Xᵢ)`. -/
noncomputable abbrev gPi [HasProductsOfShape I A] : (∀ i, B i) ⥤ A where
  obj X := ∏ᶜ fun i => (g i).obj (X i)
  map φ := Limits.Pi.map fun i => (g i).map (φ i)

variable [HasProductsOfShape I A]

/-- (3.4) `f = (fᵢ) : A → ∏ Bᵢ` is left adjoint to `g = ∏ gᵢ`. -/
noncomputable def adjPi : Functor.pi' f ⊣ gPi g := Adjunction.mkOfHomEquiv
  { homEquiv := fun Y X =>
      { toFun := fun φ => Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)
        invFun := fun ψ i => ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
        left_inv := fun φ => by
          funext i
          simp only [Limits.Pi.lift_comp_π]
          exact Equiv.symm_apply_apply _ _
        right_inv := fun ψ => by
          refine Limits.Pi.hom_ext _ _ fun i => ?_
          simp only [Limits.Pi.lift_comp_π]
          exact Equiv.apply_symm_apply _ _ }
    homEquiv_naturality_left_symm := fun h ψ => by
      funext i
      change ((adj i).homEquiv _ _).symm ((h ≫ ψ) ≫ Limits.Pi.π _ i) =
        (f i).map h ≫ ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
      rw [Category.assoc]
      exact (adj i).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := fun φ ψ => by
      refine Limits.Pi.hom_ext _ _ fun i => ?_
      change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ ((φ ≫ ψ) i)) ≫ Limits.Pi.π _ i =
        ((Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)) ≫
          Limits.Pi.map (fun i => (g i).map (ψ i))) ≫ Limits.Pi.π _ i
      rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc]
      exact (adj i).homEquiv_naturality_right _ _ }

@[reassoc (attr := simp)]
theorem adjPi_unit_π (Y : A) (j : I) :
    (adjPi f g adj).unit.app Y ≫ Limits.Pi.π _ j = (adj j).unit.app Y := by
  change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ (𝟙 ((f i).obj Y))) ≫ Limits.Pi.π _ j = _
  rw [Limits.Pi.lift_comp_π]
  exact (adj j).homEquiv_id Y

theorem adjPi_counit (X : ∀ i, B i) (j : I) :
    (adjPi f g adj).counit.app X j =
      (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫ (adj j).counit.app (X j) := by
  change ((adj j).homEquiv ((gPi g).obj X) (X j)).symm
    (𝟙 ((gPi g).obj X) ≫ Limits.Pi.π (fun i => (g i).obj (X i)) j) = _
  rw [Category.id_comp]
  exact (adj j).homEquiv_counit _ _ _

/-- (3.6) The entry `φ_ji = f_j g_i : B_i → B_j` of the matrix. -/
abbrev phi (j i : I) : B i ⥤ B j := g i ⋙ f j

/-- (3.10) `λ_kji : φ_ki → φ_kj φ_ji`, the unit `id → g_j f_j` inserted in the middle of
`f_k g_i`. -/
@[simps]
def lam (k j i : I) : phi f g k i ⟶ phi f g j i ⋙ phi f g k j where
  app X := (f k).map ((adj j).unit.app ((g i).obj X))
  naturality X Y h := by
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
    exact congrArg (f k).map ((adj j).unit.naturality ((g i).map h))

/-- (3.5)–(3.6) **The matrix.** If `f_j` commutes with `I`-indexed products, the
`j`-th component of `φ((Xᵢ))` is the product of the `φ_ji(Xᵢ)`, with projections
`f_j(prᵢ)`. -/
noncomputable def matrice (X : ∀ i, B i) (j : I) [PreservesLimitsOfShape (Discrete I) (f j)] :
    IsLimit (Fan.mk ((adjPi f g adj).toComonad.obj X j)
      fun i => (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)) :=
  (isLimitMapConeFanMkEquiv (f j) _ _) (isLimitOfPreserves (f j) (productIsProduct _))

/-- (3.9), first line: the counit of `φ` is diagonal, `ᾱ_k = α_k(X_k) ∘ pr_k`. -/
theorem counit_matrice (X : ∀ i, B i) (k : I) :
    (adjPi f g adj).toComonad.ε.app X k =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) k) ≫ (adj k).counit.app (X k) :=
  adjPi_counit f g adj X k

/-- (3.9), second line: the `(k, j, i)` entry of the comultiplication of `φ` is
`λ̄_kji = λ_kji(Xᵢ) ∘ prᵢ`. -/
theorem comult_matrice (X : ∀ i, B i) (k j i : I) :
    (adjPi f g adj).toComonad.δ.app X k ≫
        (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i))) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (lam f g adj k j i).app (X i) := by
  have h1 := adjPi_unit_π_assoc f g adj ((gPi g).obj X) j
    ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))
  have h2 := (adj j).unit.naturality (Limits.Pi.π (fun i => (g i).obj (X i)) i)
  have h3 := congrArg (f k).map (h1.trans h2.symm)
  exact (((f k).map_comp _ _).symm.trans h3).trans ((f k).map_comp _ _)

section PleinementFideles

omit [HasProductsOfShape I A] in
/-- If `g_i` is fully faithful, the diagonal entry `φ_ii = f_i g_i` is the identity
(through the counit). -/
noncomputable def diagIso (i : I) [(g i).Full] [(g i).Faithful] : phi f g i i ≅ 𝟭 (B i) :=
  asIso (adj i).counit

omit [HasProductsOfShape I A] in
/-- (3.11 b), (3.14) The unit `λ' : id_{B_i} → φ_ij φ_ji` (`i ≠ j`) when `g_i` is
fully faithful: `λ_iji` read through `φ_ii ≅ id`. -/
noncomputable def lamUnit (i j : I) [(g i).Full] [(g i).Faithful] :
    𝟭 (B i) ⟶ phi f g j i ⋙ phi f g i j :=
  (diagIso f g adj i).inv ≫ lam f g adj i j i

end PleinementFideles

end BaseProduit

section MatriceRelations

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂}
  [∀ i, Category.{v} (B i)]

variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- Right counit relation: `φ_ki(α_i) ∘ λ_kii = id`. -/
theorem lam_counit_right (k i : I) (X : B i) :
    (lam f g adj k i i).app X ≫ (phi f g k i).map ((adj i).counit.app X) = 𝟙 _ := by
  simp only [lam_app, Functor.comp_map, ← Functor.map_comp, Adjunction.right_triangle_components]
  exact (f k).map_id _

/-- Left counit relation: `α_k φ_ki ∘ λ_kki = id`. -/
theorem lam_counit_left (k i : I) (X : B i) :
    (lam f g adj k k i).app X ≫ (adj k).counit.app ((phi f g k i).obj X) = 𝟙 _ := by
  simp only [lam_app]
  exact (adj k).left_triangle_components _

/-- `l ≫ e = 𝟙` and `e ≫ i = 𝟙` give `l = i`. -/
theorem eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} (l : X ⟶ Y) (e : Y ⟶ X)
    (i : X ⟶ Y) (h1 : l ≫ e = 𝟙 X) (h2 : e ≫ i = 𝟙 Y) : l = i := by
  rw [← Category.comp_id l, ← h2, ← Category.assoc, h1, Category.id_comp]

/-- With `g_i` fully faithful, `λ_kii = φ_ki(α_i⁻¹)`. -/
theorem lam_app_right (k i : I) [(g i).Full] [(g i).Faithful] (X : B i) :
    (lam f g adj k i i).app X = (phi f g k i).map ((diagIso f g adj i).inv.app X) :=
  eq_of_comp_eq_id _ ((phi f g k i).map ((adj i).counit.app X)) _ (lam_counit_right f g adj k i X)
    (((phi f g k i).map_comp _ _).symm.trans
      ((congrArg (phi f g k i).map ((diagIso f g adj i).hom_inv_id_app X)).trans
        ((phi f g k i).map_id _)))

/-- With `g_k` fully faithful, `λ_kki = α_k⁻¹ φ_ki`. -/
theorem lam_app_left (k i : I) [(g k).Full] [(g k).Faithful] (X : B i) :
    (lam f g adj k k i).app X = (diagIso f g adj k).inv.app ((phi f g k i).obj X) :=
  eq_of_comp_eq_id _ ((adj k).counit.app ((phi f g k i).obj X)) _ (lam_counit_left f g adj k i X)
    ((diagIso f g adj k).hom_inv_id_app _)

/-- Naturality of `α_k⁻¹ : id → φ_kk`. -/
theorem diag_nat (k : I) [(g k).Full] [(g k).Faithful] {Y Z : B k} (h : Y ⟶ Z) :
    (diagIso f g adj k).inv.app Y ≫ (phi f g k k).map h = h ≫ (diagIso f g adj k).inv.app Z :=
  ((diagIso f g adj k).inv.naturality h).symm

/-- A relation `(k, i, i)`, automatic once the diagonal entry is `α_i⁻¹`. -/
theorem rel_right (k i : I) [(g i).Full] [(g i).Faithful] {Y : B k} {X : B i}
    (u : Y ⟶ (phi f g k i).obj X) :
    u ≫ (lam f g adj k i i).app X = u ≫ (phi f g k i).map ((diagIso f g adj i).inv.app X) := by
  rw [lam_app_right]

/-- A relation `(k, k, i)`, automatic once the diagonal entry is `α_k⁻¹`. -/
theorem rel_left (k i : I) [(g k).Full] [(g k).Faithful] {Y : B k} {X : B i}
    (u : Y ⟶ (phi f g k i).obj X) :
    u ≫ (lam f g adj k k i).app X = (diagIso f g adj k).inv.app Y ≫ (phi f g k k).map u := by
  rw [lam_app_left, diag_nat]

/-- The relation `(i, j, i)` with diagonal entry `α_i⁻¹` is the triangle of `λ'`. -/
theorem rel_unit (i j : I) [(g i).Full] [(g i).Faithful] (X : B i) :
    (diagIso f g adj i).inv.app X ≫ (lam f g adj i j i).app X = (lamUnit f g adj i j).app X :=
  rfl

variable [HasProductsOfShape I A]

/-- The comonad `φ = fg` over the product base. -/
noncomputable abbrev comPi : Comonad (∀ i, B i) := (adjPi f g adj).toComonad

/-- The entries `u_ki = a_k ≫ f_k(prᵢ)` of a morphism `a : X → φX`. -/
noncomputable def entree {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) (k i : I) :
    X k ⟶ (phi f g k i).obj (X i) :=
  a k ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)

/-- **The counit, entry by entry**: `a` is counital iff `α_k ∘ u_kk = id` for all `k`. -/
theorem counit_iff {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) :
    a ≫ (comPi f g adj).ε.app X = 𝟙 X ↔
      ∀ k, entree f g adj a k k ≫ (adj k).counit.app (X k) = 𝟙 _ := by
  constructor
  · intro h k
    exact (Category.assoc _ _ _).trans
      ((congrArg (a k ≫ ·) (counit_matrice f g adj X k)).symm.trans (congrFun h k))
  · intro h
    funext k
    exact (congrArg (a k ≫ ·) (counit_matrice f g adj X k)).trans
      ((Category.assoc _ _ _).symm.trans (h k))

/-- The `(j, i)` test morphisms on `φ²X`, at component `k`. -/
noncomputable abbrev test2 (X : ∀ i, B i) (k j i : I) :
    ((comPi f g adj).obj ((comPi f g adj).obj X)) k ⟶
      (phi f g k j).obj ((phi f g j i).obj (X i)) :=
  (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))

/-- Morphisms into `(φ²X)_k` are determined by the test morphisms `test2`. -/
theorem ext_phi2 [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] (X : ∀ i, B i) (k : I)
    {T : B k} (t t' : T ⟶ ((comPi f g adj).obj ((comPi f g adj).obj X)) k)
    (h : ∀ j i, t ≫ test2 f g adj X k j i = t' ≫ test2 f g adj X k j i) : t = t' := by
  have hk := (isLimitMapConeFanMkEquiv (f k) _ _)
    (isLimitOfPreserves (f k) (productIsProduct
      (fun j => (g j).obj ((f j).obj ((gPi g).obj X)))))
  refine Fan.IsLimit.hom_ext hk _ _ fun j => ?_
  have : PreservesLimitsOfShape (Discrete I) (g j) := (adj j).rightAdjoint_preservesLimits.1
  have hj := (isLimitMapConeFanMkEquiv (f j ⋙ g j ⋙ f k) _ _)
    (isLimitOfPreserves (f j ⋙ g j ⋙ f k) (productIsProduct (fun i => (g i).obj (X i))))
  refine Fan.IsLimit.hom_ext hj _ _ fun i => ?_
  have e : t ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) =
      t' ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) := by
    exact (congrArg (t ≫ ·) ((f k).map_comp _ _).symm).trans
      ((h j i).trans (congrArg (t' ≫ ·) ((f k).map_comp _ _)))
  exact (Category.assoc _ _ _).trans (e.trans (Category.assoc _ _ _).symm)

/-- `φ(a)` read on the test morphisms. -/
theorem map_test2 {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) (k j i : I) :
    (comPi f g adj).map a k ≫ test2 f g adj X k j i =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫
        (phi f g k j).map (entree f g adj a j i) := by
  change (f k).map (Limits.Pi.map fun j => (g j).map (a j)) ≫ _ = _
  simp only [test2, entree, Functor.comp_map, ← Functor.map_comp, Limits.Pi.map_π_assoc]
  exact congrArg (fun x => (f k).map (Limits.Pi.π (fun j => (g j).obj (X j)) j ≫ x))
    ((g j).map_comp _ _).symm

/-- `φ(h)` read on the projections. -/
theorem map_π {X Y : ∀ i, B i} (h : X ⟶ Y) (k i : I) :
    (comPi f g adj).map h k ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (phi f g k i).map (h i) := by
  change (f k).map (Limits.Pi.map fun j => (g j).map (h j)) ≫ _ = _
  simp only [Functor.comp_map, ← Functor.map_comp, Limits.Pi.map_π]

/-- **Coassociativity as relations between the `λ_kji`**: `a` is coassociative iff
`λ_kji ∘ u_ki = φ_kj(u_ji) ∘ u_kj` for all `k, j, i`. -/
theorem coassoc_iff [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] {X : ∀ i, B i}
    (a : X ⟶ (comPi f g adj).obj X) :
    a ≫ (comPi f g adj).δ.app X = a ≫ (comPi f g adj).map a ↔
      ∀ k j i, entree f g adj a k i ≫ (lam f g adj k j i).app (X i) =
        entree f g adj a k j ≫ (phi f g k j).map (entree f g adj a j i) := by
  have h1 : ∀ k j i, a k ≫ ((comPi f g adj).δ.app X k ≫ test2 f g adj X k j i) =
      entree f g adj a k i ≫ (lam f g adj k j i).app (X i) := fun k j i =>
    (congrArg (a k ≫ ·) (comult_matrice f g adj X k j i)).trans (Category.assoc _ _ _).symm
  have h2 : ∀ k j i, a k ≫ ((comPi f g adj).map a k ≫ test2 f g adj X k j i) =
      entree f g adj a k j ≫ (phi f g k j).map (entree f g adj a j i) := fun k j i =>
    (congrArg (a k ≫ ·) (map_test2 f g adj a k j i)).trans (Category.assoc _ _ _).symm
  constructor
  · intro h k j i
    have := congrArg (fun x => x ≫ test2 f g adj X k j i) (congrFun h k)
    exact (h1 k j i).symm.trans ((Category.assoc _ _ _).symm.trans
      (this.trans ((Category.assoc _ _ _).trans (h2 k j i))))
  · intro h
    funext k
    refine ext_phi2 f g adj X k _ _ fun j i => ?_
    exact (Category.assoc _ _ _).trans ((h1 k j i).trans ((h k j i).trans
      ((h2 k j i).symm.trans (Category.assoc _ _ _).symm)))

/-- Morphisms of coalgebras, entry by entry. -/
theorem hom_iff [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] {X Y : ∀ i, B i}
    (a : X ⟶ (comPi f g adj).obj X) (b : Y ⟶ (comPi f g adj).obj Y) (h : X ⟶ Y) :
    a ≫ (comPi f g adj).map h = h ≫ b ↔
      ∀ k i, entree f g adj a k i ≫ (phi f g k i).map (h i) = h k ≫ entree f g adj b k i := by
  have h1 : ∀ k i, a k ≫ ((comPi f g adj).map h k ≫
      (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i)) =
      entree f g adj a k i ≫ (phi f g k i).map (h i) := fun k i =>
    (congrArg (a k ≫ ·) (map_π f g adj h k i)).trans (Category.assoc _ _ _).symm
  constructor
  · intro e k i
    have := congrArg (fun x => x ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i))
      (congrFun e k)
    exact (h1 k i).symm.trans ((Category.assoc _ _ _).symm.trans
      (this.trans (Category.assoc _ _ _)))
  · intro e
    funext k
    refine Fan.IsLimit.hom_ext (matrice f g adj Y k) _ _ fun i => ?_
    exact (Category.assoc _ _ _).trans ((h1 k i).trans ((e k i).trans
      (Category.assoc _ _ _).symm))

/-- Counit of a coalgebra, with `g_k` fully faithful: the diagonal entry is `α_k⁻¹`. -/
theorem entree_diag {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X)
    (ha : a ≫ (comPi f g adj).ε.app X = 𝟙 X) (k : I) [(g k).Full] [(g k).Faithful] :
    entree f g adj a k k = (diagIso f g adj k).inv.app (X k) :=
  eq_of_comp_eq_id _ ((adj k).counit.app (X k)) _ ((counit_iff f g adj a).1 ha k)
    ((diagIso f g adj k).hom_inv_id_app _)

end MatriceRelations

section Quadruplets

variable {A : Type u₁} [Category.{v} A] {B : WalkingPair → Type u₂}
  [∀ i, Category.{v} (B i)]

variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

variable [(g .left).Full] [(g .left).Faithful] [(g .right).Full] [(g .right).Faithful]

/-- (pages 9–10) A quadruple `(X', X'', u', u'')`, `u' : X' → φ'(X'')`,
`u'' : X'' → φ''(X')`, subject to the two triangles `λ'(X') = φ'(u'') ∘ u'` and
`λ''(X'') = φ''(u') ∘ u''`. -/
structure Quadruplet where
  X' : B .left
  X'' : B .right
  u' : X' ⟶ (phi f g .left .right).obj X''
  u'' : X'' ⟶ (phi f g .right .left).obj X'
  tri' : (lamUnit f g adj .left .right).app X' = u' ≫ (phi f g .left .right).map u''
  tri'' : (lamUnit f g adj .right .left).app X'' = u'' ≫ (phi f g .right .left).map u'

namespace Quadruplet

variable {f g adj}

/-- A morphism of quadruples: a pair `(h', h'')` commuting with `u'` and `u''`. -/
@[ext]
structure Hom (P Q : Quadruplet f g adj) where
  h' : P.X' ⟶ Q.X'
  h'' : P.X'' ⟶ Q.X''
  w' : P.u' ≫ (phi f g .left .right).map h'' = h' ≫ Q.u' := by cat_disch
  w'' : P.u'' ≫ (phi f g .right .left).map h' = h'' ≫ Q.u'' := by cat_disch

attribute [reassoc] Hom.w' Hom.w''

instance : Category (Quadruplet f g adj) where
  Hom := Hom
  id P := { h' := 𝟙 _, h'' := 𝟙 _ }
  comp a b := { h' := a.h' ≫ b.h', h'' := a.h'' ≫ b.h''
                w' := by
                  rw [Functor.map_comp, ← Category.assoc, a.w', Category.assoc, b.w',
                    Category.assoc]
                w'' := by
                  rw [Functor.map_comp, ← Category.assoc, a.w'', Category.assoc, b.w'',
                    Category.assoc] }

@[ext]
theorem hom_ext {P Q : Quadruplet f g adj} {a b : P ⟶ Q} (h' : a.h' = b.h')
    (h'' : a.h'' = b.h'') : a = b := Hom.ext h' h''

end Quadruplet

variable [HasProductsOfShape WalkingPair A]

variable [∀ j, PreservesLimitsOfShape (Discrete WalkingPair) (f j)]

/-- A morphism given by its two components. -/
def pairHom {X Y : ∀ i, B i} (h' : X .left ⟶ Y .left) (h'' : X .right ⟶ Y .right) : X ⟶ Y
  | .left => h'
  | .right => h''

/-- (pages 9–10) A coalgebra of `φ` gives the quadruple of its off-diagonal entries. -/
noncomputable def versQuadruplets : (comPi f g adj).Coalgebra ⥤ Quadruplet f g adj where
  obj C :=
    { X' := C.A .left
      X'' := C.A .right
      u' := entree f g adj C.a .left .right
      u'' := entree f g adj C.a .right .left
      tri' := by
        have := (coassoc_iff f g adj C.a).1 C.coassoc .left .right .left
        rw [entree_diag f g adj C.a C.counit] at this
        exact this
      tri'' := by
        have := (coassoc_iff f g adj C.a).1 C.coassoc .right .left .right
        rw [entree_diag f g adj C.a C.counit] at this
        exact this }
  map {C D} h :=
    { h' := h.f .left
      h'' := h.f .right
      w' := (hom_iff f g adj C.a D.a h.f).1 h.h .left .right
      w'' := (hom_iff f g adj C.a D.a h.f).1 h.h .right .left }

/-- An object of `B' × B''` given by its two components. -/
def pairObj (X' : B .left) (X'' : B .right) : ∀ i, B i
  | .left => X'
  | .right => X''

variable {f g adj} in
/-- The matrix of a quadruple: `α⁻¹` on the diagonal, `u'` and `u''` off it. -/
noncomputable def entreesQ (Q : Quadruplet f g adj) :
    ∀ k i, pairObj Q.X' Q.X'' k ⟶ (phi f g k i).obj (pairObj Q.X' Q.X'' i)
  | .left, .left => (diagIso f g adj .left).inv.app Q.X'
  | .left, .right => Q.u'
  | .right, .left => Q.u''
  | .right, .right => (diagIso f g adj .right).inv.app Q.X''

variable {f g adj} in
/-- The coalgebra structure defined by a quadruple. -/
noncomputable def structQ (Q : Quadruplet f g adj) :
    pairObj Q.X' Q.X'' ⟶ (comPi f g adj).obj (pairObj Q.X' Q.X'') := fun k =>
  Fan.IsLimit.lift (matrice f g adj (pairObj Q.X' Q.X'') k) (entreesQ Q k)

/-- The entries of `structQ Q` are those of `entreesQ Q`. -/
theorem entree_structQ (Q : Quadruplet f g adj) (k i : WalkingPair) :
    entree f g adj (structQ Q) k i = entreesQ Q k i :=
  Fan.IsLimit.fac (matrice f g adj (pairObj Q.X' Q.X'') k) _ i

variable {f g adj} in
/-- **The quadruple defines a coalgebra**: the triangles are all the coassociativity. -/
noncomputable def coalgQ (Q : Quadruplet f g adj) : (comPi f g adj).Coalgebra where
  A := pairObj Q.X' Q.X''
  a := structQ Q
  counit := (counit_iff f g adj _).2 fun k => by
    rw [entree_structQ]
    cases k
    · exact (diagIso f g adj .left).inv_hom_id_app Q.X'
    · exact (diagIso f g adj .right).inv_hom_id_app Q.X''
  coassoc := (coassoc_iff f g adj _).2 fun k j i => by
    rw [entree_structQ, entree_structQ, entree_structQ]
    cases k <;> cases j <;> cases i
    · exact rel_right f g adj _ _ _
    · exact rel_left f g adj _ _ Q.u'
    · exact (rel_unit f g adj _ _ _).trans Q.tri'
    · exact rel_right f g adj _ _ Q.u'
    · exact rel_right f g adj _ _ Q.u''
    · exact (rel_unit f g adj _ _ _).trans Q.tri''
    · exact rel_left f g adj _ _ Q.u''
    · exact rel_right f g adj _ _ _

instance : (versQuadruplets f g adj).Faithful where
  map_injective {C D} a b e := by
    refine Comonad.Coalgebra.Hom.ext (funext fun j => ?_)
    cases j
    · exact congrArg Quadruplet.Hom.h' e
    · exact congrArg Quadruplet.Hom.h'' e

instance : (versQuadruplets f g adj).Full where
  map_surjective {C D} q := by
    refine ⟨⟨pairHom q.h' q.h'', (hom_iff f g adj C.a D.a _).2 fun k i => ?_⟩, rfl⟩
    cases k <;> cases i
    · rw [entree_diag f g adj C.a C.counit, entree_diag f g adj D.a D.counit]
      exact diag_nat f g adj _ q.h'
    · exact q.w'
    · exact q.w''
    · rw [entree_diag f g adj C.a C.counit, entree_diag f g adj D.a D.counit]
      exact diag_nat f g adj _ q.h''

instance : (versQuadruplets f g adj).EssSurj where
  mem_essImage Q := ⟨coalgQ Q, ⟨
    { hom := { h' := 𝟙 _, h'' := 𝟙 _
               w' := ((congrArg (_ ≫ ·) ((phi f g .left .right).map_id _)).trans
                 ((Category.comp_id _).trans
                   ((entree_structQ f g adj Q .left .right).trans (Category.id_comp _).symm)))
               w'' := ((congrArg (_ ≫ ·) ((phi f g .right .left).map_id _)).trans
                 ((Category.comp_id _).trans
                   ((entree_structQ f g adj Q .right .left).trans (Category.id_comp _).symm))) }
      inv := { h' := 𝟙 _, h'' := 𝟙 _
               w' := ((congrArg (_ ≫ ·) ((phi f g .left .right).map_id _)).trans
                 ((Category.comp_id _).trans ((entree_structQ f g adj Q .left .right).symm.trans
                   (Category.id_comp _).symm)))
               w'' := ((congrArg (_ ≫ ·) ((phi f g .right .left).map_id _)).trans
                 ((Category.comp_id _).trans ((entree_structQ f g adj Q .right .left).symm.trans
                   (Category.id_comp _).symm))) }
      hom_inv_id := by ext <;> exact Category.comp_id _
      inv_hom_id := by ext <;> exact Category.comp_id _ }⟩⟩

/-- **Pages 9–10: coalgebras of `φ` are the quadruples.** For two factors with `g'`, `g''`
fully faithful and `f'`, `f''` commuting with binary products, the category of coalgebras
of `φ` is equivalent to the category of quadruples `(X', X'', u', u'')`. -/
instance versQuadruplets_isEquivalence : (versQuadruplets f g adj).IsEquivalence where

/-- **Pages 9–10: the description of `A` by quadruples.** If moreover `f = (f', f'')` is
comonadic, `A` is equivalent to the category of quadruples, by
`Y ↦ (f'Y, f''Y, f'(η''_Y), f''(η'_Y))` (`quadruplet_u'`, `quadruplet_u''`). -/
theorem quadruplets [(Comonad.comparison (adjPi f g adj)).IsEquivalence] :
    (Comonad.comparison (adjPi f g adj) ⋙ versQuadruplets f g adj).IsEquivalence := by
  sorry

end Quadruplets

end Grothendieck.Folder19

end

-- From Challenge/Folder21.lean
@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Grothendieck.Folder21.Stack

universe v' u'

variable {X : Type*} [TopologicalSpace X] (F : (Opens X)ᵒᵖ ⥤ Cat.{v', u'})

/-- The restriction functor `𝓕(V) ⥤ 𝓕(W)` along `W ≤ V`. -/
def res {V W : Opens X} (h : W ≤ V) : F.obj (op V) ⥤ F.obj (op W) :=
  (F.map (homOfLE h).op).toFunctor

theorem res_comp {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) :
    res F h₁ ⋙ res F h₂ = res F (h₂.trans h₁) := by
  simp only [res, ← Cat.Hom.comp_toFunctor, ← F.map_comp]
  rfl

theorem obj_res_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : F.obj (op U)) :
    (res F h₂).obj ((res F h₁).obj f) = (res F (h₂.trans h₁)).obj f :=
  Functor.congr_obj (res_comp F h₁ h₂) f

variable {F}

/-- Restriction `ρ_{S ≤ T}` on the presheaf `T ↦ Hom(f|T, g|T)` of a pair of objects over `V`. -/
def ρ {V T S : Opens X} {h : T ≤ V} (h₁ : S ≤ T) {f g : F.obj (op V)}
    (a : (res F h).obj f ⟶ (res F h).obj g) :
    (res F (h₁.trans h)).obj f ⟶ (res F (h₁.trans h)).obj g :=
  eqToHom (obj_res_res F h h₁ f).symm ≫ (res F h₁).map a ≫ eqToHom (obj_res_res F h h₁ g)

variable (F)

/-- `(P₃)` relative to `Y`: restriction is an equivalence. -/
def P3 (Y : Set X) : Prop :=
  ∀ ⦃V T : Opens X⦄ (h : T ≤ V), (T : Set X) = (V : Set X) \ Y → (res F h).IsEquivalence

/-- Faithfulness at `x` of `Pseudolim_W 𝓕(W) ⥤ Pseudolim_W 𝓕(W - W ∩ cl{x})`, unfolded:
two morphisms over a neighbourhood of `x` that agree off `cl{x}` agree near `x`. -/
def FaithfulAt (x : X) : Prop :=
  ∀ ⦃W T : Opens X⦄ (h : T ≤ W), x ∈ W → (T : Set X) = (W : Set X) \ closure {x} →
    ∀ ⦃f g : F.obj (op W)⦄ (a b : f ⟶ g), (res F h).map a = (res F h).map b →
      ∃ (W' : Opens X) (h' : W' ≤ W), x ∈ W' ∧ (res F h').map a = (res F h').map b

/-- Fullness at `x`, unfolded: a morphism off `cl{x}` agrees, near `x` and off `cl{x}`,
with a morphism defined near `x`. -/
def FullAt (x : X) : Prop :=
  ∀ ⦃W T : Opens X⦄ (h : T ≤ W), x ∈ W → (T : Set X) = (W : Set X) \ closure {x} →
    ∀ ⦃f g : F.obj (op W)⦄ (c : (res F h).obj f ⟶ (res F h).obj g),
      ∃ (W' : Opens X) (h' : W' ≤ W), x ∈ W' ∧
        ∃ (a : (res F h').obj f ⟶ (res F h').obj g) (S : Opens X) (h₁ : S ≤ W') (h₂ : S ≤ T),
          (S : Set X) = (W' : Set X) \ closure {x} ∧ ρ h₁ a = ρ h₂ c

/-- Essential surjectivity at `x`, unfolded: an object off `cl{x}` is, near `x` and off
`cl{x}`, isomorphic to the restriction of an object defined near `x`. -/
def EssSurjAt (x : X) : Prop :=
  ∀ ⦃W T : Opens X⦄ (_ : T ≤ W), x ∈ W → (T : Set X) = (W : Set X) \ closure {x} →
    ∀ e : F.obj (op T), ∃ (W' : Opens X) (_ : W' ≤ W), x ∈ W' ∧
      ∃ (f₀ : F.obj (op W')) (S : Opens X) (h₁ : S ≤ W') (h₂ : S ≤ T),
        (S : Set X) = (W' : Set X) \ closure {x} ∧ Nonempty ((res F h₁).obj f₀ ≅ (res F h₂).obj e)

/-- Descent of morphisms for covers by two opens (the Hom presheaves are sheaves for them). -/
structure IsBinaryPrestack : Prop where
  ext : ∀ ⦃A B T : Opens X⦄ (hA : A ≤ T) (hB : B ≤ T), (T : Set X) = (A : Set X) ∪ B →
    ∀ ⦃f g : F.obj (op T)⦄ (u v : f ⟶ g), (res F hA).map u = (res F hA).map v →
      (res F hB).map u = (res F hB).map v → u = v
  glue : ∀ ⦃A B D T : Opens X⦄ (hA : A ≤ T) (hB : B ≤ T) (hDA : D ≤ A) (hDB : D ≤ B),
    (T : Set X) = (A : Set X) ∪ B → (D : Set X) = (A : Set X) ∩ B →
    ∀ ⦃f g : F.obj (op T)⦄ (α : (res F hA).obj f ⟶ (res F hA).obj g)
      (β : (res F hB).obj f ⟶ (res F hB).obj g), ρ hDA α = ρ hDB β →
      ∃ u : f ⟶ g, (res F hA).map u = α ∧ (res F hB).map u = β

/-- A binary prestack in which objects also glue along covers by two opens. -/
structure IsBinaryStack : Prop extends IsBinaryPrestack F where
  glueObj : ∀ ⦃A B D T : Opens X⦄ (hA : A ≤ T) (hB : B ≤ T) (hDA : D ≤ A) (hDB : D ≤ B),
    (T : Set X) = (A : Set X) ∪ B → (D : Set X) = (A : Set X) ∩ B →
    ∀ (a : F.obj (op A)) (b : F.obj (op B)), Nonempty ((res F hDA).obj a ≅ (res F hDB).obj b) →
      ∃ t : F.obj (op T), Nonempty ((res F hA).obj t ≅ a) ∧ Nonempty ((res F hB).obj t ≅ b)

variable {F}

variable [NoetherianSpace X] [QuasiSober X]

/-- **Proposition 7, `(P₃)`**, for a stack (binary covers suffice): restriction to `V - Y` is
an equivalence for every open `V` iff the induced functor on germs at each `x ∈ Y` is one. -/
theorem proposition7_P3 (hF : IsBinaryStack F) {Y : Set X} (hY : IsClosed Y) :
    P3 F Y ↔ ∀ x ∈ Y, (FullAt F x ∧ FaithfulAt F x) ∧ EssSurjAt F x := by
  sorry

end Grothendieck.Folder21.Stack

end

-- From Challenge/Folder22.lean
@[expose] public section

namespace Grothendieck.Folder22

open TensorProduct LinearMap

universe u

variable {A : Type u} [CommRing A]

section SeveralVariablesSmooth

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {σ : Type*} [Finite σ]
  [DecidableEq σ]

/-- **Page 23's Proposition in `n ≥ 1` variables, formal smoothness**: for a field `K` over `R`
with `Ω_{K/R}` infinite-dimensional, `K⟦t₁, …, tₙ⟧` with the discrete topology is not formally
smooth over `K`. As for `n = 1`: a formally smooth `S` would give, by Jacobi–Zariski, a retraction
`r` of `S ⊗_K Ω_{K/R} → Ω_{S/R}` (`retraction_of_formallySmooth`), and `r ∘ d_{S/R}` would be a
derivation inducing `d_{K/R}`, which `no_derivation_mv` excludes. -/
theorem not_formallySmooth_mv (i₀ : σ) (h : ¬ Module.Finite K Ω[K⁄R]) :
    ¬ Algebra.FormallySmooth K (MvPowerSeries σ K) := by
  sorry

end SeveralVariablesSmooth

end Grothendieck.Folder22

end

-- From Challenge/Folder29.lean
@[expose] public section

open Matrix

namespace Folder29

variable {C C' : Type*} [Fintype C] [Fintype C']

/-- The map `ℤ_ℓ^C → ℤ_ℓ^{C'}` of an integer matrix with rows indexed by `C'` and columns
by `C`. -/
noncomputable def inertiaMap (N : Matrix C' C ℤ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (C → ℤ_[ℓ]) → (C' → ℤ_[ℓ]) :=
  (N.map (Int.cast : ℤ → ℤ_[ℓ])).mulVec

/-- **The criterion of page 120.** The integer matrix `N` is bijective over `ℤ_ℓ` for every
prime `ℓ ≠ p` iff `card C = card C'` and, the columns being matched with the rows by some
bijection, `det N = ± p^k`. -/
theorem criterion [DecidableEq C'] {p : ℕ} (hp : p = 1 ∨ p.Prime) (N : Matrix C' C ℤ) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → Function.Bijective (inertiaMap N ℓ)) ↔
      Fintype.card C = Fintype.card C' ∧ ∃ e : C' ≃ C, ∃ k : ℕ,
        (N.submatrix id e).det = p ^ k ∨ (N.submatrix id e).det = -(p ^ k : ℤ) := by
  sorry

end Folder29

end

-- From Challenge/Folder37.lean
@[expose] public section

namespace Grothendieck.Folder37

open Polynomial

variable (k : Type*) [Field k]

/-- `B[T]` with `B = k[X₀, X₁, …]`. -/
abbrev P := (MvPolynomial ℕ k)[X]

/-- `Aₙ = B[T]/(T^{n+1})`, a type of its own so that its ring structure has a single
source. -/
def An (n : ℕ) : Type _ := P k ⧸ Ideal.span {(X : P k) ^ (n + 1)}

noncomputable instance (n : ℕ) : CommRing (An k n) :=
  fast_instance% Ideal.Quotient.commRing _

/-- The reduction `B[T] → Aₙ`. -/
noncomputable def mkA (n : ℕ) : P k →+* An k n := Ideal.Quotient.mk _

/-- The generator `XₗTˡ` of `B[T]`. -/
noncomputable def gen (l : ℕ) : P k := C (MvPolynomial.X l) * X ^ l

/-- `Jₙ = (X₀, X₁T, …, XₙTⁿ) ⊂ Aₙ`. -/
noncomputable def Jn (n : ℕ) : Ideal (An k n) :=
  Ideal.span (Set.range fun l : Fin (n + 1) => mkA k n (gen k l))

open TensorProduct in
/-- **The counterexample.** For any commutative ring `A` and any ring maps `A → Aₙ`
(the page's `A = B[[T]]` with its reductions), no finitely presented `A`-module `M`
has `Aₙ ⊗_A M ≅ Mₙ = Aₙ/Jₙ` for every `n`. -/
theorem no_finitePresentation_inducing (A : Type*) [CommRing A] (f : ∀ n, A →+* An k n)
    (M : Type*) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] :
    ¬ ∀ n, letI := (f n).toAlgebra
      Nonempty ((An k n) ⊗[A] M ≃ₗ[An k n] (An k n ⧸ Jn k n)) := by
  sorry

end Grothendieck.Folder37

end

-- From Challenge/Folder39.lean
@[expose] public section

namespace Grothendieck.Folder39.Henselian

open MvPowerSeries

variable {k : Type*} [CommRing k]

/-- Conditions (I), (S), (R), (H) of pages 9–11 on a family `A n ⊆ k[[t₁, …, tₙ]]`; (R) is
built in, each `A n` being a unital subring. (S) is taken in its strong form (constants
allowed in `φ`), (H) with « isomorphisme formel » read as « has a two-sided inverse for
substitution ». -/
structure IsFormalClass (A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)) : Prop where
  /-- (I) -/
  X_mem : ∀ n (i : Fin n), X i ∈ A n
  /-- (S) -/
  subst_mem : ∀ {n m : ℕ} {φ : MvPowerSeries (Fin n) k} {f : Fin n → MvPowerSeries (Fin m) k},
    φ ∈ A n → (∀ i, f i ∈ A m) → (∀ i, IsNilpotent (constantCoeff (f i))) → subst f φ ∈ A m
  /-- (H) -/
  inv_mem : ∀ {n : ℕ} {f g : Fin n → MvPowerSeries (Fin n) k}, (∀ i, f i ∈ A n) →
    (∀ i, IsNilpotent (constantCoeff (f i))) → (∀ i, IsNilpotent (constantCoeff (g i))) →
    (∀ i, subst g (f i) = X i) → (∀ i, subst f (g i) = X i) → ∀ i, g i ∈ A n

variable {A : ∀ n : ℕ, Subring (MvPowerSeries (Fin n) k)}

/-- Corollary 3 of page 12 (the implicit function theorem in the class), under (I), (S), (R),
(H) alone: if `P ∈ A_{n+1}` (variables `Z, t₁, …, tₙ`) has `P(0) = 0` and `∂P/∂Z (0)` a unit
of `k`, the unique `F` with `F(0) = 0` and `P(F(t), t) = 0` lies in `A_n`. -/
theorem implicit_mem (hA : IsFormalClass A) {n : ℕ} {P : MvPowerSeries (Fin (n + 1)) k}
    (hP : P ∈ A (n + 1)) (h0 : constantCoeff P = 0)
    (h1 : IsUnit (coeff (Finsupp.single 0 1) P)) {F : MvPowerSeries (Fin n) k}
    (hF0 : constantCoeff F = 0)
    (hF : subst (Fin.cons F X : Fin (n + 1) → MvPowerSeries (Fin n) k) P = 0) : F ∈ A n := by
  sorry

end Grothendieck.Folder39.Henselian

end

-- From Challenge/Folder40.lean
@[expose] public section

namespace Grothendieck.Folder40

open Polynomial IsLocalRing

section PowerSeries

variable {k : Type*} [Field k]

/-- The cusp `S = k[[X]][T]/(T^n - X²)`. -/
abbrev Cusp (k : Type*) [Field k] (n : ℕ) := AdjoinRoot (X ^ n - C (PowerSeries.X ^ 2 : (PowerSeries k)))

theorem not_isDVR_cusp_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    ¬ ∃ _ : IsDomain (Cusp k n), IsDiscreteValuationRing (Cusp k n) := by
  sorry

end PowerSeries

end Grothendieck.Folder40

end

-- From Challenge/Folder41.lean
@[expose] public section

namespace Grothendieck.Folder41

open Topology

section Topologie

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `φ(y)` is the generic point of the (irreducible, non-empty) fibre `f⁻¹(y)`:
it lies over `y` and specialises to every point over `y`. -/
def SectionGenerique (f : X → Y) (φ : Y → X) : Prop :=
  ∀ y, f (φ y) = y ∧ ∀ x, f x = y → φ y ⤳ x

variable {f : X → Y} {φ : Y → X} (hφ : SectionGenerique f φ)

include hφ

end Topologie

section Schemas

open AlgebraicGeometry

/-- **Proposition 1.** For a morphism of schemes locally of finite presentation
whose fibres are irreducible and non-empty with generic points `φ(y)`, the four
conditions (i), (ii), (iii), (iii bis) are equivalent. -/
theorem proposition1 {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] (φ : Y → X)
    (hφ : SectionGenerique f φ) :
    List.TFAE [Continuous φ, IsOpenMap f, ∀ y y', y' ⤳ y → φ y' ⤳ φ y, GeneralizingMap f] := by
  sorry

end Schemas

end Grothendieck.Folder41

end

-- From Challenge/Folder42.lean
@[expose] public section

namespace Grothendieck.Folder42.Reseau

open AlgebraicGeometry CategoryTheory Limits Topology TopologicalSpace

universe u

variable {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- **A homomorphism of réseaux of local rings `p(X) → p(Y)` over `p(S)` (page 1).** An
application of the specialisation orders, increasing (`x ⤳ x'`, « `x'` specialises `x` »,
gives `φ x ⤳ φ x'`), lying over `S`, with a local homomorphism `𝒪_{Y,φ(x)} → 𝒪_{X,x}` at each
point, compatible with the generisation maps, and compatible with the structure maps to the
local rings of `S`. The localisation axiom of a réseau is a property of `p(X)` and `p(Y)`, which
come from schemes, so it is not a field here. -/
structure ReseauHom where
  toFun : X → Y
  mono : ∀ {x x' : X}, x ⤳ x' → toFun x ⤳ toFun x'
  liesOver : ∀ x, sX x = sY (toFun x)
  stalk : ∀ x, Y.presheaf.stalk (toFun x) ⟶ X.presheaf.stalk x
  isLocalHom : ∀ x, IsLocalHom (stalk x).hom
  compat : ∀ {x x' : X} (h : x ⤳ x'),
    stalk x' ≫ X.presheaf.stalkSpecializes h = Y.presheaf.stalkSpecializes (mono h) ≫ stalk x
  overStalk : ∀ x, sY.stalkMap (toFun x) ≫ stalk x =
    S.presheaf.stalkSpecializes (Inseparable.of_eq (liesOver x)).specializes ≫ sX.stalkMap x

attribute [instance] ReseauHom.isLocalHom

variable {sX sY}

/-- The réseau homomorphism of an `S`-morphism. -/
noncomputable def toReseau (f : X ⟶ Y) (hf : f ≫ sY = sX) : ReseauHom sX sY where
  toFun := f
  mono h := f.base.hom.map_specializes h
  liesOver x := by rw [← hf]; rfl
  stalk x := f.stalkMap x
  isLocalHom x := inferInstance
  compat h := (f.stalkSpecializes_stalkMap _ _ h).symm
  overStalk x := by
    subst hf
    rw [Scheme.Hom.stalkMap_comp]
    simp

/-- **Corollaire 3, the theorem of page 2 in the edition's form.** For `X` locally Noetherian and
`Y` locally of finite type and separated over `S`, `f ↦ p(f)` is a bijection from the
`S`-morphisms `X → Y` onto the homomorphisms of réseaux of local rings `p(X) → p(Y)` over
`p(S)`. -/
theorem toReseau_bijective [IsLocallyNoetherian X] [LocallyOfFiniteType sY] [IsSeparated sY] :
    Function.Bijective (fun f : {f : X ⟶ Y // f ≫ sY = sX} => toReseau f.1 f.2) := by
  sorry

end Grothendieck.Folder42.Reseau

end

-- From Challenge/Folder43.lean
@[expose] public section

open Polynomial

namespace Grothendieck.Folder43

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- Left composition with `F`: `Σ aᵢ t^{pⁱ} ↦ Σ aᵢᵖ t^{p^{i+1}}`. -/
noncomputable def Fr : (ℕ →₀ R) →+ (ℕ →₀ R) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp
    (Finsupp.mapRange.addMonoidHom (frobenius R p).toAddMonoidHom)

/-- `D = F − 1`, `f ↦ fᵖ − f`. -/
noncomputable def D : (ℕ →₀ R) →+ (ℕ →₀ R) := Fr R p - AddMonoidHom.id _

/-- `c ↦ [c]ᵢ`, the class of `(i, c)` in the perfection. -/
def mkHom (i : ℕ) : R →+ PerfectClosure R p where
  toFun c := PerfectClosure.mk R p (i, c)
  map_zero' := PerfectClosure.mk_zero_right R p i
  map_add' a b := by
    rw [PerfectClosure.mk_add_mk]
    simp only
    rw [← iterate_map_add]
    exact PerfectClosure.R.sound R p i i (a + b) _ rfl

/-- `Φ (a) = Σ [aᵢ]ᵢ`. -/
noncomputable def Φ : (ℕ →₀ R) →+ PerfectClosure R p := Finsupp.liftAddHom (mkHom R p)

/-- **The kernel of `Φ` is the image of `F − 1`.** -/
theorem ker_Φ : (Φ R p).ker = (D R p).range := by
  sorry

end Grothendieck.Folder43

end

-- From Challenge/Folder44.lean
@[expose] public section

namespace Grothendieck.Folder44

/-- `Δ = {±3e₁, ±3e₂, ±(e₁ + e₂), ±(e₁ - e₂)}`. -/
def roots : Finset (ℤ × ℤ) :=
  {(3, 0), (-3, 0), (0, 3), (0, -3), (1, 1), (-1, -1), (1, -1), (-1, 1)}

/-- **The three axioms do not give integrality.** There is a finite reduced `Δ`
generating `ℤ²`, with a symmetry for each root, whose (unique) symmetry of the form
`x ↦ x - f(x) a` has a non-integral Cartan number. -/
theorem axioms_not_integral :
    AddSubgroup.closure (roots : Set (ℤ × ℤ)) = ⊤ ∧
    (∀ a ∈ roots, -a ∈ roots) ∧
    (∀ a ∈ roots, ∀ b ∈ roots, ∀ q : ℚ,
      (b.1 : ℚ) = q * a.1 ∧ (b.2 : ℚ) = q * a.2 → q = 1 ∨ q = -1) ∧
    (∀ a ∈ roots, ∃ S : (ℤ × ℤ) ≃+ (ℤ × ℤ), S a = -a ∧ ∀ x ∈ roots, S x ∈ roots) ∧
    ∀ f : ℤ × ℤ →+ ℚ, f (3, 0) = 2 →
      (∀ x ∈ roots, ∃ y ∈ roots, (x.1 : ℚ) - f x * 3 = y.1 ∧ (x.2 : ℚ) = y.2) →
      ¬ ∃ n : ℤ, f (1, 1) = n := by
  sorry

end Grothendieck.Folder44

end

-- From Challenge/Folder46.lean
@[expose] public section

open Finset IsLocalRing

namespace Grothendieck.Folder46

section Cocycles

variable {Γ A : Type*} [Group Γ] [Ring A] [MulSemiringAction Γ A]

/-- A (nonabelian) 1-cocycle of `Γ` with values in `Aˣ`: `c(gh) = c(g) · g(c(h))`. -/
def IsCocycle (c : Γ → Aˣ) : Prop :=
  ∀ g h, (c (g * h) : A) = c g * g • (c h : A)

variable [Fintype Γ]

variable {B : Type*} [Ring B] [MulSemiringAction Γ B]

end Cocycles

section LocalRing

variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]

variable [IsLocalRing O]

variable {Γ B : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ A] [Ring B]
  [MulSemiringAction Γ B]

/-- **Page 90, injectivity**, `A` finite over `𝒪` and `p ∤ |Γ|`: two cocycles `Γ → A*` whose
images in `B = A/𝔪A` (or any surjective equivariant image with kernel in `𝔪A`) are cohomologous
are cohomologous. -/
theorem injective [Module.Finite O A] (hp : ¬ ringChar (ResidueField O) ∣ Fintype.card Γ)
    (π : A →+* B) (hπ : Function.Surjective π) (hequiv : ∀ (g : Γ) (a : A), π (g • a) = g • π a)
    (hker : ∀ x, π x = 0 → x ∈ maximalIdeal O • (⊤ : Submodule O A)) {c c' : Γ → Aˣ}
    (hc : IsCocycle c) (hc' : IsCocycle c')
    (hπc : ∃ v : Bˣ, ∀ g, π (c g) = ↑v⁻¹ * π (c' g) * g • (v : B)) :
    ∃ u : Aˣ, ∀ g, (c g : A) = ↑u⁻¹ * c' g * g • (u : A) := by
  sorry

end LocalRing

end Grothendieck.Folder46

end

-- From Challenge/Folder50.lean
@[expose] public section

namespace Grothendieck.Folder50

open Polynomial Finset

/-- The frame of pages 6–10 at one object and one class `ξ` with `φ_ξ` a
`ℚ`-isomorphism, transported to `E = End(A)` by `ψ(η) = φ_ξ⁻¹ φ_η`; the star is
the Rosati involution. -/
structure Frame (E N : Type*) [Ring E] [StarRing E] [AddCommGroup N] (r : ℕ) where
  /-- `η ↦ φ_ξ⁻¹ φ_η`. -/
  ψ : N →+ E
  ψ_injective : Function.Injective ψ
  /-- The classes are antisymmetric, so their images are Rosati-symmetric. -/
  star_ψ : ∀ η, star (ψ η) = ψ η
  /-- The pullback `α*η`. -/
  pb : E → N → N
  ψ_pb : ∀ α η, ψ (pb α η) = star α * ψ η * α
  /-- The class `ξ`. -/
  ξ : N
  ψ_ξ : ψ ξ = 1
  /-- The intersection form of (e). -/
  I : MultilinearMap ℤ (fun _ : Fin r => N) ℤ
  /-- The degree of (e) 3). -/
  ν : E → ℤ
  I_pb : ∀ u (v : Fin r → N), I (fun i => pb u (v i)) = ν u * I v
  I_ξ : I (fun _ => ξ) ≠ 0

namespace Frame

variable {E N : Type*} [Ring E] [StarRing E] [AddCommGroup N] {r : ℕ} (F : Frame E N r)

/-- `D_ξ(α, β) = (α + β)*ξ − α*ξ − β*ξ`. -/
def D (α β : E) : N := F.pb (α + β) F.ξ - F.pb α F.ξ - F.pb β F.ξ

/-- `D_ξ(α) = D_ξ(α, 1)`. -/
def Dξ (α : E) : N := F.D α 1

/-- The weight of each summand of `(α + n)*ξ = n²ξ + n D_ξ(α) + α*ξ`. -/
def wt : Fin 3 → ℕ := ![2, 1, 0]

/-- The three summands. -/
def sel (α : E) : Fin 3 → N := ![F.ξ, F.Dξ α, F.pb α F.ξ]

/-- The polynomial `P` with `P(n) = ν(α + n)`, over `ℚ`. -/
noncomputable def charPoly (α : E) : ℚ[X] :=
  C ((F.I fun _ => F.ξ : ℤ) : ℚ)⁻¹ *
    ∑ f : Fin r → Fin 3, C ((F.I fun i => F.sel α (f i) : ℤ) : ℚ) * X ^ (∑ i, wt (f i))

/-- `σᵢ(α)`, the coefficient of `n^{2r − i}` in `ν(α + n)`. -/
noncomputable def σ (i : ℕ) (α : E) : ℚ := (F.charPoly α).coeff (2 * r - i)

/-- `tr(α) = σ₁(α)`. -/
noncomputable def tr (α : E) : ℚ := F.σ 1 α

/-- **The trace formula** (head of page 8), for a symmetric intersection form:
`tr(α) · I(ξ^r) = r · I(ξ^{r−1}, D_ξ(α))`. -/
theorem tr_mul_I {m : ℕ} (F : Frame E N (m + 1))
    (hsym : ∀ (σ : Equiv.Perm (Fin (m + 1))) (v : Fin (m + 1) → N), F.I (v ∘ σ) = F.I v)
    (α : E) :
    F.tr α * ((F.I fun _ => F.ξ : ℤ) : ℚ) =
      (m + 1) * ((F.I (Function.update (fun _ => F.ξ) 0 (F.Dξ α)) : ℤ) : ℚ) := by
  sorry

end Frame

end Grothendieck.Folder50

end

-- From Challenge/Folder53.lean
@[expose] public section

open MvPolynomial

namespace Grothendieck.Folder53

variable {K ι : Type*} [Field K]

/-- The polynomial law: `law m a v i = m i (a, v)`, the variables `inl j` for `a`, `inr j`
for `v`. -/
noncomputable def law (m : ι → MvPolynomial (ι ⊕ ι) K) (a v : ι → K) : ι → K :=
  fun i => eval (Sum.elim a v) (m i)

variable [IsAlgClosed K] [Finite ι]

/-- A monoid of `K`-points of an affine variety with a polynomial law, whose left translations
are injective, is a group (the reading of folder 53, page 21, over an algebraically closed
field). -/
theorem isUnit_of_isLeftCancelMul {M : Type*} [Monoid M] [IsLeftCancelMul M]
    (φ : M → ι → K) (hφ : Function.Injective φ) (I : Ideal (MvPolynomial ι K))
    (hI : Set.range φ = zeroLocus K I) (m : ι → MvPolynomial (ι ⊕ ι) K)
    (hm : ∀ x y, φ (x * y) = law m (φ x) (φ y)) (x : M) : IsUnit x := by
  sorry

end Grothendieck.Folder53

open Pointwise

end

-- From Challenge/Folder55.lean
@[expose] public section

open CategoryTheory TopologicalSpace Opposite

namespace Grothendieck.Folder55

universe u

variable {X : TopCat.{u}} {F : TopCat.Presheaf (Type u) X}

/-- A subsheaf of a presheaf of types `F`: for each open `U` a set of sections over `U`,
stable under restriction, and *local* — a section lies in it as soon as it does locally. -/
structure Subsheaf (F : TopCat.Presheaf (Type u) X) where
  /-- The sections over `U` lying in the subsheaf. -/
  sections : ∀ U : Opens X, Set (F.obj (op U))
  restrict : ∀ {U V : Opens X} (h : V ≤ U) {s : F.obj (op U)},
    s ∈ sections U → F.map (homOfLE h).op s ∈ sections V
  isLocal : ∀ (U : Opens X) (s : F.obj (op U)),
    (∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ F.map (homOfLE h).op s ∈ sections V) →
      s ∈ sections U

namespace Subsheaf

@[ext]
theorem ext {S T : Subsheaf F} (h : ∀ U, S.sections U = T.sections U) : S = T := by
  cases S; cases T; congr; exact funext h

instance : PartialOrder (Subsheaf F) where
  le S T := ∀ U, S.sections U ⊆ T.sections U
  le_refl _ _ := subset_rfl
  le_trans _ _ _ h₁ h₂ U := (h₁ U).trans (h₂ U)
  le_antisymm _ _ h₁ h₂ := ext fun U => (h₁ U).antisymm (h₂ U)

/-- `S` and `T` agree on the open `W`: they have the same sections over every open of `W`. -/
def AgreeOn (S T : Subsheaf F) (W : Opens X) : Prop :=
  ∀ V : Opens X, V ≤ W → S.sections V = T.sections V

/-- The germs at `x` of the sections of `S`, a subset of the stalk `F_x`. -/
def germs (S : Subsheaf F) (x : X) : Set (F.stalk x) :=
  {g | ∃ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)), s ∈ S.sections U ∧ F.germ U x hx s = g}

end Subsheaf

open Subsheaf

/-- **Lemme B, with the identity principle replaced by the uniformity it is meant to give.**
On a quasi-compact space, let `S` be an increasing sequence of subsheaves. Suppose that
* at every point the germs stabilise (hypothesis (iv): see `germs_stabilize_of_noetherian`);
* (uniformity) for every point `x` and every index `k`, there is an open neighbourhood `W` of
  `x` such that every later `S l` with the same germs at `x` as `S k` agrees with `S k` on `W`.
Then the sequence is stationary. -/
theorem stationary_of_germs [CompactSpace X] (S : ℕ → Subsheaf F) (hS : Monotone S)
    (hgerm : ∀ x : X, ∃ k₀, ∀ k ≥ k₀, (S k).germs x = (S k₀).germs x)
    (huniform : ∀ (x : X) (k : ℕ), ∃ W : Opens X, x ∈ W ∧
      ∀ l ≥ k, (S l).germs x = (S k).germs x → AgreeOn (S l) (S k) W) :
    ∃ k₀, ∀ k ≥ k₀, S k = S k₀ := by
  sorry

end Grothendieck.Folder55

end

-- From Challenge/Folder62.lean
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

end

-- From Challenge/Folder63.lean
@[expose] public section

open Polynomial

namespace Grothendieck.Folder63

/-- `ℤ[ζ]`, `ζ` a primitive cube root of unity. -/
abbrev R := AdjoinRoot (X ^ 2 + X + 1 : ℤ[X])

/-- `ζ`. -/
noncomputable abbrev ζ : R := AdjoinRoot.root _

/-- `P = (2, t)`. -/
noncomputable def P : Ideal R[X] := Ideal.span {C 2, X}

/-- The four values `0, 1, ζ, ζ²`. -/
noncomputable def α : Fin 4 → R := ![0, 1, ζ, ζ ^ 2]

/-- The four branches `t + 2α` of `V(c₄)` through `a`. -/
noncomputable def branch (i : Fin 4) : R[X] := X + 2 * C (α i)

/-- **The four tangents are pairwise distinct**: for `i ≠ j`, `a · branch i + b · branch j ∈ P²`
forces `a, b ∈ P`. -/
theorem tangents_distinct (i j : Fin 4) (hij : i ≠ j) (a b : R[X])
    (h : a * branch i + b * branch j ∈ P ^ 2) : a ∈ P ∧ b ∈ P := by
  sorry

end Grothendieck.Folder63

end

-- From Challenge/Folder64.lean
@[expose] public section

namespace Grothendieck.Folder64

open Finset

section Field

variable {K : Type*} [Field K] [DecidableEq K]

/-- The four vertices other than `∞` and `−1`. -/
def quad (i : K) : Finset K := {0, 1, i, -i}

variable {i : K}

/-- Page 48: an automorphism fixing `∞` and `−1` is `z ↦ a z + (a − 1)`; if it maps
`{0, 1, i, −i}` into itself, then `5 (a − 1) = 0`. -/
theorem fixer_five (hi : i ^ 2 = -1) (h2 : (2 : K) ≠ 0) (a : K)
    (h : ∀ z ∈ quad i, a * z + (a - 1) ∈ quad i) : (5 : K) * (a - 1) = 0 := by
  sorry

end Field

end Grothendieck.Folder64

end

-- From Challenge/Folder67.lean
@[expose] public section

namespace Grothendieck.Folder67

open CategoryTheory

universe v u

variable (k : Type u) [Ring k]

section Basics

variable {k}

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- `M` is `2`-regular: multiplication by `2` is injective. -/
def TwoRegular (M : Type*) [AddCommGroup M] : Prop :=
  ∀ x : M, 2 • x = 0 → x = 0

/-- The linear map `x ↦ 2x`. -/
def twice (k : Type u) [Ring k] (M : Type*) [AddCommGroup M] [Module k M] : M →ₗ[k] M :=
  (2 : ℕ) • LinearMap.id

@[simp] lemma twice_apply (x : M) : twice k M x = 2 • x := rfl

/-- The submodule `2M`. -/
abbrev two (k : Type u) [Ring k] (M : Type*) [AddCommGroup M] [Module k M] : Submodule k M :=
  LinearMap.range (twice k M)

lemma mem_two {x : M} : x ∈ two k M ↔ ∃ y, 2 • y = x := by
  simp [two]

lemma two_smul_mem_two (y : M) : 2 • y ∈ two k M := mem_two.2 ⟨y, rfl⟩

end Basics

/-- A `2`-regular `k`-module with an involution. -/
structure InvMod where
  /-- the module `M` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- the involution -/
  σ : carrier →ₗ[k] carrier
  σ_σ : ∀ x, σ (σ x) = x
  reg : TwoRegular carrier

attribute [instance] InvMod.isAddCommGroup InvMod.isModule

namespace InvMod

variable {k}

/-- The `+1`-eigenmodule `M₊ = Ker(1 - σ)`. -/
def plus (X : InvMod.{v} k) : Submodule k X.carrier := LinearMap.ker (LinearMap.id - X.σ)

/-- The `-1`-eigenmodule `M₋ = Ker(1 + σ)`. -/
def minus (X : InvMod.{v} k) : Submodule k X.carrier := LinearMap.ker (LinearMap.id + X.σ)

variable (X : InvMod.{v} k)

lemma mem_plus {x : X.carrier} : x ∈ X.plus ↔ X.σ x = x := by
  rw [plus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, eq_comm]

lemma mem_minus {x : X.carrier} : x ∈ X.minus ↔ X.σ x = -x := by
  rw [minus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_neg_eq, eq_comm]

/-- Page 90: `2x = (x + σx) + (x - σx)`, with `x + σx ∈ M₊` and `x - σx ∈ M₋`. -/
lemma add_σ_mem_plus (x : X.carrier) : x + X.σ x ∈ X.plus := by
  rw [mem_plus, map_add, X.σ_σ, add_comm]

lemma sub_σ_mem_minus (x : X.carrier) : x - X.σ x ∈ X.minus := by
  rw [mem_minus, map_sub, X.σ_σ, neg_sub]

end InvMod

namespace InvMod

variable {k}

variable (X : InvMod.{v} k)

/-- The submodule `{(p, q) | p + q ∈ 2M}` of `M₊ × M₋`. -/
def S : Submodule k (X.plus × X.minus) :=
  (two k X.carrier).comap (X.plus.subtype.coprod X.minus.subtype)

/-- The submodule `m ⊂ M₊/2M₊ × M₋/2M₋` of page 90: the image of `2M`. -/
def m : Submodule k ((X.plus ⧸ two k X.plus) × (X.minus ⧸ two k X.minus)) :=
  X.S.map ((two k X.plus).mkQ.prodMap (two k X.minus).mkQ)

/-- `(p̄, q̄) ∈ m` if and only if `p + q ∈ 2M`. -/
theorem mk_mem_m_iff (p : X.plus) (q : X.minus) :
    (Submodule.Quotient.mk p, Submodule.Quotient.mk q) ∈ X.m ↔
      (p : X.carrier) + q ∈ two k X.carrier := by
  refine ⟨?_, fun h => ⟨(p, q), h, rfl⟩⟩
  rintro ⟨⟨p', q'⟩, hS, he⟩
  simp only [LinearMap.prodMap_apply, Submodule.mkQ_apply, Prod.mk.injEq,
    Submodule.Quotient.eq] at he
  obtain ⟨hp, hq⟩ := he
  have hS' : (p' : X.carrier) + q' ∈ two k X.carrier := hS
  have lift : ∀ (N : Submodule k X.carrier) (x : N), x ∈ two k N →
      (x : X.carrier) ∈ two k X.carrier := by
    intro N x hx
    obtain ⟨y, hy⟩ := mem_two.1 hx
    exact mem_two.2 ⟨y, by rw [← hy]; rfl⟩
  have h1 := lift _ _ hp
  have h2 := lift _ _ hq
  simp only [Submodule.coe_sub] at h1 h2
  rw [show (p : X.carrier) + q = ((p' : X.carrier) + q') - (p' - p) - (q' - q) by abel]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hS' h1) h2

/-- The preimage of `m` in `M₊ × M₋` (the module that `build` makes of `triple`). -/
def Nx : Submodule k (X.plus × X.minus) :=
  X.m.comap ((two k X.plus).mkQ.prodMap (two k X.minus).mkQ)

/-- `x ↦ (x + σx, x - σx)`, from `M` into the module rebuilt from its triple. -/
def toBuild : X.carrier →ₗ[k] X.Nx :=
  LinearMap.codRestrict X.Nx
    (LinearMap.prod
      (LinearMap.codRestrict X.plus (LinearMap.id + X.σ) (fun x => X.add_σ_mem_plus x))
      (LinearMap.codRestrict X.minus (LinearMap.id - X.σ) (fun x => X.sub_σ_mem_minus x)))
    (fun x => by
      change (Submodule.Quotient.mk (⟨x + X.σ x, X.add_σ_mem_plus x⟩ : X.plus),
        Submodule.Quotient.mk (⟨x - X.σ x, X.sub_σ_mem_minus x⟩ : X.minus)) ∈ X.m
      rw [mk_mem_m_iff]
      change (x + X.σ x) + (x - X.σ x) ∈ two k X.carrier
      rw [show (x + X.σ x) + (x - X.σ x) = 2 • x by rw [two_nsmul]; abel]
      exact two_smul_mem_two x)

lemma toBuild_bijective : Function.Bijective X.toBuild := by
  sorry

end InvMod

end Grothendieck.Folder67

end

-- From Challenge/Folder68.lean
@[expose] public section

open Module Pointwise

namespace Grothendieck.Folder68

/-- `H` is a closed half-space of `V` bounded by the hyperplane `W`: there is a nonzero
linear form `f` with kernel `W` and `H = {f ≥ 0}`. The opposite half-space is `-H`. -/
def IsHalfSpace {V : Type*} [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) (H : Set V) :
    Prop :=
  ∃ f : V →ₗ[ℝ] ℝ, LinearMap.ker f = W ∧ f ≠ 0 ∧ H = {v | 0 ≤ f v}

/-- A *theory of orientation* (page 49): a functor `Ω` from the groupoid of finite-dimensional
real vector spaces (in `Type`) and their linear isomorphisms to two-element sets (a), an
identification `Ω(0) ≃ {±1}` (b), and for every hyperplane `W ⊂ V` and closed half-space `H`
bounded by `W` a Stokes map `St_H : Ω(V) → Ω(W)` (c), natural in `(V, H)`, subject to the two
axioms: `St_H` is bijective, and `St_{-H} = τ ∘ St_H`, which on a two-element set says
`St_{-H} ω ≠ St_H ω`. -/
structure Theory where
  /-- The two-element set `Ω(V)`. -/
  Ω : (V : Type) → [AddCommGroup V] → [Module ℝ V] → [FiniteDimensional ℝ V] → Type
  /-- The action of linear isomorphisms. -/
  map : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂], (V ≃ₗ[ℝ] V₂) → Ω V → Ω V₂
  map_refl : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : Ω V),
    map (LinearEquiv.refl ℝ V) ω = ω
  map_trans : ∀ {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    [AddCommGroup V₃] [Module ℝ V₃] [FiniteDimensional ℝ V₃]
    (e₁ : V₁ ≃ₗ[ℝ] V₂) (e₂ : V₂ ≃ₗ[ℝ] V₃) (ω : Ω V₁), map (e₁.trans e₂) ω = map e₂ (map e₁ ω)
  card : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V], Nat.card (Ω V) = 2
  /-- `Ω(0) ≃ {±1}`. -/
  zero : Ω (Fin 0 → ℝ) ≃ ℤˣ
  /-- The Stokes map of a half-space. -/
  St : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V), IsHalfSpace W H → Ω V → Ω W
  St_natural : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂] (e : V ≃ₗ[ℝ] V₂)
    (W : Submodule ℝ V) (W₂ : Submodule ℝ V₂) (H : Set V) (H₂ : Set V₂)
    (hH : IsHalfSpace W H) (hH₂ : IsHalfSpace W₂ H₂) (hW : W.map (e : V →ₗ[ℝ] V₂) = W₂)
    (_ : e '' H = H₂) (ω : Ω V),
    St W₂ H₂ hH₂ (map e ω) = map (e.ofSubmodules W W₂ hW) (St W H hH ω)
  St_bijective : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H), Function.Bijective (St W H hH)
  St_neg : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H) (hH' : IsHalfSpace W (-H))
    (ω : Ω V), St W (-H) hH' ω ≠ St W H hH ω

/-- A morphism of theories: a natural transformation compatible with b) and c). -/
structure Hom (T T' : Theory) where
  app : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V], T.Ω V → T'.Ω V
  natural : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂] (e : V ≃ₗ[ℝ] V₂) (ω : T.Ω V),
    app V₂ (T.map e ω) = T'.map e (app V ω)
  zero : ∀ ω, T'.zero (app _ ω) = T.zero ω
  stokes : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H) (ω : T.Ω V),
    T'.St W H hH (app V ω) = app W (T.St W H hH ω)

/-- **Theorem b)** (page 49): between two theories of orientation there is exactly one
morphism, and its components are bijective. -/
theorem exists_unique_hom (T T' : Theory) :
    ∃ φ : Hom T T', (∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
      Function.Bijective (φ.app V)) ∧
      ∀ ψ : Hom T T', ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
        ψ.app V = φ.app V := by
  sorry

end Grothendieck.Folder68

end

-- From Challenge/Folder69.lean
@[expose] public section

namespace Grothendieck.Folder69

open Equiv

/-- The fifteen pairs `i < j` of `{0, …, 5}`, in lexicographic order. -/
def pairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The pair of `c_{ij}`. -/
def cp (v : Fin 27) : ℕ × ℕ := pairs.getD (v.val - 12) (0, 0)

/-- Do two of the twenty-seven lines meet? -/
def meets (u v : Fin 27) : Bool :=
  if u.val < 12 ∧ v.val < 12 then
    (u.val < 6 ∧ 6 ≤ v.val ∧ u.val + 6 ≠ v.val) || (v.val < 6 ∧ 6 ≤ u.val ∧ v.val + 6 ≠ u.val)
  else if u.val < 12 then (cp v).1 = u.val % 6 || (cp v).2 = u.val % 6
  else if v.val < 12 then (cp u).1 = v.val % 6 || (cp u).2 = v.val % 6
  else (cp u).1 ≠ (cp v).1 ∧ (cp u).1 ≠ (cp v).2 ∧ (cp u).2 ≠ (cp v).1 ∧ (cp u).2 ≠ (cp v).2

/-- The graph `C` of the twenty-seven lines. -/
def C : SimpleGraph (Fin 27) where
  Adj u v := meets u v = true
  symm := ⟨fun u v h =>
    ((show ∀ u v : Fin 27, meets u v = meets v u by decide +kernel) u v).symm.trans h⟩
  loopless := ⟨fun u h => by
    rw [(show ∀ u : Fin 27, meets u u = false by decide +kernel) u] at h
    exact Bool.false_ne_true h⟩

/-- The marked triangle `t = {a₀, b₁, c₀₁}`. -/
def t : Finset (Fin 27) := {0, 7, 12}

/-- The same count for the graph automorphisms `C ≃g C` that preserve `t`. -/
theorem card_aut : Nat.card {f : C ≃g C // ∀ v, f v ∈ t ↔ v ∈ t} = 1152 := by
  sorry

end Grothendieck.Folder69

end

-- From Challenge/Folder70.lean
@[expose] public section

namespace Grothendieck.Folder70

section General

variable {R : Type*} [CommRing R] (α : R)

/-- The antipodism `ι` of page 91, (17). -/
def iota (p : R × R × R) : R × R × R :=
  ((-1 - α) - p.1, 1 - (-1 - α) - p.2.1, 1 - (-1 - α) - p.2.2)

/-- The twelve vertices of page 75 in the order `s₀, s₁, s₂, s₃, s'₃, s''₃` and their
antipodes `ι s₀, …, ι s''₃`. -/
def vert : Fin 12 → R × R × R :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1 - α, -(-1 - α), 1), (0, -(-1 - α), 1),
    iota α (0, 0, 0), iota α (1, 0, 0), iota α (0, 1, 0), iota α (0, 0, 1),
    iota α (-1 - α, -(-1 - α), 1), iota α (0, -(-1 - α), 1)]

variable {α}

end General

end Grothendieck.Folder70

namespace Grothendieck.Folder70

section Quadric

open Matrix

variable {R : Type*} [CommRing R] {α : R}

/-- A quadratic function `a x² + b y² + c z² + u yz + v zx + w xy + d x + e y + f z + k` on
`R³`, by its ten coefficients. -/
@[ext] structure QuadFn (R : Type*) where
  (a b c u v w d e f k : R)

/-- The value of a quadratic function at a point. -/
def QuadFn.eval (Q : QuadFn R) (p : R × R × R) : R :=
  Q.a * p.1 ^ 2 + Q.b * p.2.1 ^ 2 + Q.c * p.2.2 ^ 2 + Q.u * (p.2.1 * p.2.2)
    + Q.v * (p.2.2 * p.1) + Q.w * (p.1 * p.2.1) + Q.d * p.1 + Q.e * p.2.1 + Q.f * p.2.2 + Q.k

/-- A scalar multiple of a quadratic function. -/
def QuadFn.smul (r : R) (Q : QuadFn R) : QuadFn R :=
  ⟨r * Q.a, r * Q.b, r * Q.c, r * Q.u, r * Q.v, r * Q.w, r * Q.d, r * Q.e, r * Q.f, r * Q.k⟩

variable (α) in
/-- The coefficients of the invariant function `q` of pages 95 and 101. -/
def qFn : QuadFn R := ⟨1, 1, 1, -α, 1, 1, -1, -1, -1, 0⟩

/-- **Page 101: uniqueness of the quadric.** Over any commutative ring with `α² + α − 1 = 0`,
a quadratic function vanishing at the nine vertices `s₀, s₁, s₂, s₃, s'₃, s''₃, ι s₀, ι s₁,
ι s₂` is `a · q`, `a` its coefficient of `x²`: the `9 × 9` minor of the linear system is
`13α + 21`, a unit of `ℤ[α]` (of inverse `13α − 8`). -/
theorem quadric_unique (h : α ^ 2 + α - 1 = 0) (Q : QuadFn R)
    (hQ : ∀ i : Fin 12, i.val < 9 → Q.eval (vert α i) = 0) : Q = QuadFn.smul Q.a (qFn α) := by
  sorry

end Quadric

end Grothendieck.Folder70

end

-- From Challenge/Folder72.lean
@[expose] public section

namespace Grothendieck.Folder72

universe u

variable {R : Type u} [CommRing R]

variable (n : ℕ) (μ β : ℕ → R)

/-- The coordinate of index `k`, zero beyond `n + 1`. -/
def co (k : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  if h : k < n + 2 then LinearMap.proj (⟨k, h⟩ : Fin (n + 2)) else 0

/-- The basis vector `e_k` (`e₀ = s₀`, `e_{i+1} = aᵢ`). -/
def e (k : ℕ) : Fin (n + 2) → R := fun j => if (j : ℕ) = k then 1 else 0

/-- The form `a'ᵢ`: `⟨a_{i−1}, a'ᵢ⟩ = 1`, `⟨aᵢ, a'ᵢ⟩ = μᵢ`, `⟨a_{i+1}, a'ᵢ⟩ = βᵢ`. -/
def F (i : ℕ) : (Fin (n + 2) → R) →ₗ[R] R :=
  co n i + μ i • co n (i + 1) + β i • co n (i + 2)

/-- The pseudo-reflection `τᵢ = id + a'ᵢ ⊗ aᵢ`. -/
def τ (i : ℕ) : Module.End R (Fin (n + 2) → R) :=
  1 + (F n μ β i).smulRight (e n (i + 1))

variable {n}

/-- `(y_{top−m}, y_{top−m+1})` for the solution of `F_k y = 0` (`k < top`) with
`y_top = 1`, `y_k = 0` for `k > top`. -/
def cc (top : ℕ) : ℕ → R × R
  | 0 => (1, 0)
  | m + 1 => (-(μ (top - 1 - m) * (cc top m).1 + β (top - 1 - m) * (cc top m).2), (cc top m).1)

/-- The coordinates of the back-substituted vector with top index `top`. -/
def y (top k : ℕ) : R := if k ≤ top then (cc μ β top (top - k)).1 else 0

variable {μ β}

variable (μ β) in
/-- The vector with coordinates `y top`. -/
def vec (top : ℕ) : Fin (n + 2) → R := fun j => y μ β top j

variable (n μ β)

/-- `c̃`: killed by every `a'ᵢ`, coordinate `1` on `aₙ`. -/
def ct : Fin (n + 2) → R := vec μ β (n + 1)

variable {n μ β}

section Invariant

/-- `Z'ᵢ = H₀ ∩ ⋯ ∩ Hᵢ`. -/
def Zp (n : ℕ) (μ β : ℕ → R) (i : ℕ) : Submodule R (Fin (n + 2) → R) where
  carrier := {x | ∀ k ≤ i, F n μ β k x = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- `Z*ᵢ = Lin(h_{i+1}, …, hₙ) = Lin(e_{i+2}, …, e_{n+1})`. -/
def Zs (n : ℕ) (i : ℕ) : Submodule R (Fin (n + 2) → R) where
  carrier := {x | ∀ k ≤ i + 1, co n k x = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; simp
  smul_mem' := by intro c x hx k hk; simp [hx k hk]

/-- The hyperplane at infinity `C`, `π = 0`. -/
def Vh (n : ℕ) : Submodule R (Fin (n + 2) → R) := LinearMap.ker (co n 0)

/-- Stability under all the `τᵢ`. -/
def Invariant (n : ℕ) (μ β : ℕ → R) (W : Submodule R (Fin (n + 2) → R)) : Prop :=
  ∀ i ≤ n, ∀ w ∈ W, τ n μ β i w ∈ W

variable {K : Type u} [Field K] {μ' β' : ℕ → K}

/-- **Page 79.** The subspaces stable under all the `τᵢ`. -/
theorem invariant_iff (W : Submodule K (Fin (n + 2) → K)) :
    Invariant n μ' β' W ↔
      W = ⊥ ∨ W = ⊤ ∨ W = K ∙ ct n μ' β' ∨ W = Vh n ∨
        ∃ i < n, β' i = 0 ∧ (W = Zp n μ' β' i ∨ W = Zs n i) := by
  sorry

end Invariant

end Grothendieck.Folder72

end

-- From Challenge/Folder73.lean
@[expose] public section

namespace Folder73

open Matrix

variable {k : Type*}

section Polygon

variable [Field k] {n : ℕ} [NeZero n]

/-- The multipliers of an `n`-gon given by its sides (page 25, the relation `(∗)`):
`λ_i u_{i-1} - λ_{i+1}(u_i + u_{i+1}) + λ_{i+2} u_{i+2} = 0` for all `i`. -/
def IsMult (u : ZMod n → Fin 2 → k) (l : ZMod n → k) : Prop :=
  ∀ i, l i • u (i - 1) - l (i + 1) • (u i + u (i + 1)) + l (i + 2) • u (i + 2) = 0

end Polygon

section EarArea

variable [Field k] {n : ℕ} [NeZero n]

/-- The space `N(u_*)` of multipliers. -/
def multSpace (u : ZMod n → Fin 2 → k) : Submodule k (ZMod n → k) where
  carrier := {l | IsMult u l}
  add_mem' {a b} ha hb i := by
    have h := congrArg₂ (· + ·) (ha i) (hb i)
    simp only [add_zero] at h
    rw [← h]
    simp only [Pi.add_apply, add_smul]
    abel
  zero_mem' i := by simp
  smul_mem' c a ha i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← smul_sub, ← smul_add, ha i, smul_zero]

variable (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)

include hu

end EarArea

section FourCases

variable [Field k] {n : ℕ} [NeZero n] (u : ZMod n → Fin 2 → k) (hu : ∀ i, u i ≠ 0)

include hu

/-- **Page 28, the Théorème: the four cases** (`|k| > n`). -/
theorem four_cases (hk : (n : ℕ∞) < ENat.card k) :
    multSpace u = ⊥ ∨
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧ Module.finrank k (multSpace u) = 1) ∨
      ((∃ l ∈ multSpace u, ∀ i, l i ≠ 0) ∧ Module.finrank k (multSpace u) = 2) ∨
      (multSpace u ≠ ⊥ ∧ (∃ i, ∀ l ∈ multSpace u, l i = 0) ∧
        Module.finrank k (multSpace u) = 1) := by
  sorry

end FourCases

end Folder73

end

-- From Challenge/Folder74.lean
@[expose] public section

namespace Grothendieck.Folder74

noncomputable section

open Function

section Axioms

variable {V : Type*} (G : SimpleGraph V)

/-- Axiom 1: every edge lies in a unique triangle. -/
def Axiom1 : Prop := ∀ x y, G.Adj x y → ∃! z, G.Adj x z ∧ G.Adj y z

end Axioms

universe u

/-- The points of `∐ Ẽ_α`. -/
abbrev Pt (X : Fin 3 → Type u) : Type u := Σ α, X α

/-- The data of the Scholie of page 96 on three sets `Ẽ_α = X α`: fixed-point-free
involutions `σ_α`, and a set `T ⊆ ∏ Ẽ_α` of triples (the upper triangles). -/
structure Scholie (X : Fin 3 → Type u) where
  σ : ∀ α, X α → X α
  σσ : ∀ α s, σ α (σ α s) = s
  σne : ∀ α s, σ α s ≠ s
  T : Set (∀ α, X α)

namespace Scholie

variable {X : Fin 3 → Type u} (D : Scholie X)

/-- The involution `σ` on `∐ Ẽ_α`. -/
def sg (p : Pt X) : Pt X := ⟨p.1, D.σ p.1 p.2⟩

/-- Two points of distinct `Ẽ`'s are linked when a triple of `T` contains both. -/
def Lk (p q : Pt X) : Prop := p.1 ≠ q.1 ∧ ∃ τ ∈ D.T, τ p.1 = p.2 ∧ τ q.1 = q.2

/-- Condition (*): the projections of `T` on two factors are injective. -/
def Star : Prop :=
  ∀ τ ∈ D.T, ∀ ρ ∈ D.T, ∀ α β, α ≠ β → τ α = ρ α → τ β = ρ β → τ = ρ

/-- Condition `β_Γ̃` (page 101, with Prop. 5 of page 98): of the two points of an
orbit of `σ_α`, exactly one is linked to a given point of `Ẽ_β`, `β ≠ α`. -/
def Beta : Prop := ∀ p q : Pt X, p.1 ≠ q.1 → (D.Lk (D.sg p) q ↔ ¬ D.Lk p q)

/-- Condition (***) = (Ka) of the margin of page 96, in the form used here: three
triples `τ, ρ₁, ρ₂ ∈ T` through the pairs `(s_α, s_β)`, `(s_α, s_γ)`, `(s_β, s_γ)`
of one family `(s_α, s_β, s_γ)` coincide. -/
def Ka : Prop :=
  ∀ α β γ : Fin 3, α ≠ β → α ≠ γ → β ≠ γ → ∀ τ ∈ D.T, ∀ ρ₁ ∈ D.T, ∀ ρ₂ ∈ D.T,
    τ α = ρ₁ α → τ β = ρ₂ β → ρ₁ γ = ρ₂ γ → τ = ρ₁

theorem sg_sg (p : Pt X) : D.sg (D.sg p) = p := by
  obtain ⟨α, s⟩ := p; simp [sg, D.σσ]

theorem sg_ne (p : Pt X) : D.sg p ≠ p := by
  obtain ⟨α, s⟩ := p
  intro h
  simp only [sg, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact D.σne α s h

theorem Lk_symm {p q : Pt X} (h : D.Lk p q) : D.Lk q p := by
  obtain ⟨hne, τ, hτ, h1, h2⟩ := h
  exact ⟨Ne.symm hne, τ, hτ, h2, h1⟩

theorem Lk_irrefl (p : Pt X) : ¬ D.Lk p p := fun h => h.1 rfl

/-- Adjacency on `t₀ ⊔ ∐ Ẽ_α` (Scholie, 2°) α)–δ)). -/
def Adj : Fin 3 ⊕ Pt X → Fin 3 ⊕ Pt X → Prop
  | .inl α, .inl β => α ≠ β
  | .inl α, .inr p => p.1 = α
  | .inr p, .inl α => p.1 = α
  | .inr p, .inr q => q = D.sg p ∨ D.Lk p q

/-- The graph of the Scholie, on `t₀ ⊔ ∐ Ẽ_α`. -/
def graph : SimpleGraph (Fin 3 ⊕ Pt X) where
  Adj := D.Adj
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [Adj] at h ⊢
    · exact Ne.symm h
    · exact h
    · exact h
    · rcases h with rfl | h
      · exact Or.inl (D.sg_sg _).symm
      · exact Or.inr (D.Lk_symm h)⟩
  loopless := ⟨fun a h => by
    cases a <;> simp only [Adj] at h
    · exact h rfl
    · rcases h with h | h
      · exact D.sg_ne _ h.symm
      · exact D.Lk_irrefl _ h⟩

@[simp] theorem adj_inl_inl (α β : Fin 3) :
    D.graph.Adj (.inl α) (.inl β) ↔ α ≠ β := Iff.rfl

@[simp] theorem adj_inl_inr (α : Fin 3) (p : Pt X) :
    D.graph.Adj (.inl α) (.inr p) ↔ p.1 = α := Iff.rfl

@[simp] theorem adj_inr_inl (α : Fin 3) (p : Pt X) :
    D.graph.Adj (.inr p) (.inl α) ↔ p.1 = α := Iff.rfl

@[simp] theorem adj_inr_inr (p q : Pt X) :
    D.graph.Adj (.inr p) (.inr q) ↔ q = D.sg p ∨ D.Lk p q := Iff.rfl

/-- Under (*) and `β_Γ̃`, the graph satisfies axiom 1 if and only if (Ka) holds;
it then satisfies axiom 2. -/
theorem axiom1_iff_ka (hS : D.Star) (hB : D.Beta) : Axiom1 D.graph ↔ D.Ka := by
  sorry

end Scholie

end

end Grothendieck.Folder74

end

-- From Challenge/Folder76.lean
@[expose] public section

namespace Grothendieck.Folder76

open MulAction

variable {G : Type*} [Group G] {n : ℕ}

/-- `G_K`, the subgroup generated by the `σᵢ`, `i ∈ K`. -/
def gen (σ : Fin (n + 1) → G) (K : Set (Fin (n + 1))) : Subgroup G :=
  Subgroup.closure (σ '' K)

/-- `N_H = G_{Δₙ ∖ H}`. -/
def N (σ : Fin (n + 1) → G) (H : Set (Fin (n + 1))) : Subgroup G := gen σ Hᶜ

lemma gen_mono (σ : Fin (n + 1) → G) {K K' : Set (Fin (n + 1))} (h : K ⊆ K') :
    gen σ K ≤ gen σ K' :=
  Subgroup.closure_mono (Set.image_mono h)

lemma N_anti (σ : Fin (n + 1) → G) {H H' : Set (Fin (n + 1))} (h : H ⊆ H') :
    N σ H' ≤ N σ H :=
  gen_mono σ (Set.compl_subset_compl.mpr h)

variable (σ : Fin (n + 1) → G) (X : Type*) [MulAction G X]

/-- `D(H) = X / N_H`, the flags of type `H`. -/
abbrev D (H : Set (Fin (n + 1))) : Type _ := orbitRel.Quotient (N σ H) X

variable {σ X}

/-- Restriction `D(H') → D(H)` for `H ⊆ H'`. -/
def res {H H' : Set (Fin (n + 1))} (h : H ⊆ H') : D σ X H' → D σ X H :=
  Quotient.map' id fun x y hxy => by
    rw [orbitRel_apply] at hxy ⊢
    obtain ⟨g, rfl⟩ := hxy
    exact ⟨⟨g, N_anti σ h g.2⟩, rfl⟩

/-- **Lemme (pages 27–28)**, under the margin's hypotheses: the largest element
`i` of `H` lies in `H'`, and `H ∩ H'` is an initial segment of `H'`. Two flags
of types `H` and `H'` with the same restriction to `H ∩ H'` are the
restrictions of one flag of type `H ∪ H'`: `D(H ∪ H') → D(H) ×_{D(H ∩ H')} D(H')`
is surjective. -/
theorem flag_lemma (hσ : ∀ i j : Fin (n + 1), (i : ℕ) + 2 ≤ j → Commute (σ i) (σ j))
    {H H' : Set (Fin (n + 1))} (i : Fin (n + 1)) (hiH : i ∈ H) (hmax : ∀ j ∈ H, j ≤ i)
    (hiH' : i ∈ H') (hinit : ∀ j ∈ H', ∀ k ∈ H ∩ H', j ≤ k → j ∈ H)
    (a : D σ X H) (b : D σ X H')
    (hab : res Set.inter_subset_left a = res Set.inter_subset_right b) :
    ∃ c : D σ X (H ∪ H'), res Set.subset_union_left c = a ∧
      res Set.subset_union_right c = b := by
  sorry

end Grothendieck.Folder76

end

-- From Challenge/Folder77.lean
@[expose] public section

namespace Grothendieck.Folder77

open MvPolynomial Matrix

/-- The polar matrix of the quadratic form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` over a
commutative ring `R`. -/
def polarOf {R : Type*} [CommRing R] {n : ℕ} (y : Sym2 (Fin n) → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then 2 * y s(i, i) else y s(i, j)

section

open Finset

/-- The fixed-point-free involutions of `Fin m`, that is, the perfect matchings. -/
def fpfInv (m : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  univ.filter fun σ => σ * σ = 1 ∧ ∀ i, σ i ≠ i

end

/-- The hafnian of the off-diagonal variables: the sum over the perfect matchings of
`Fin m` (the fixed-point-free involutions) of the products of the `Yᵢⱼ`. -/
noncomputable def hafnian (m : ℕ) : MvPolynomial (Sym2 (Fin m)) ℤ :=
  ∑ σ ∈ fpfInv m, ∏ i ∈ Finset.univ.filter (fun i => i < σ i), X s(i, σ i)

/-- **Pages 68–71, every even rank, over any base.** There is `C ∈ ℤ[Y]` such that for every
commutative ring `R` and every form `Σ yᵢ xᵢ² + Σ_{i<j} yᵢⱼ xᵢ xⱼ` of rank `2n` over `R`,
`(-1)ⁿ det P(y) = B(y)² - 4 C(y)`. -/
theorem disc_even_rank (n : ℕ) :
    ∃ C : MvPolynomial (Sym2 (Fin (2 * n))) ℤ, ∀ {R : Type*} [CommRing R]
      (y : Sym2 (Fin (2 * n)) → R),
        (-1) ^ n * (polarOf y).det = aeval y (hafnian (2 * n)) ^ 2 - 4 * aeval y C := by
  sorry

end Grothendieck.Folder77

end

-- From Challenge/Folder78.lean
@[expose] public section

namespace Grothendieck.Folder78

open Polynomial Polynomial.Chebyshev

section Poly

variable (R : Type*) [CommRing R]

/-- The polynomial `F_n` of page 109: `F_{2m} = S_{m−1}`, `F_{2m+1} = S_m + S_{m−1}`, with
`S` the rescaled Chebyshev polynomials of the second kind. -/
noncomputable def F (n : ℤ) : R[X] :=
  if Even n then S R (n / 2 - 1) else S R (n / 2) + S R (n / 2 - 1)

end Poly

section Map

variable {k : Type*} [CommRing k]

/-- `u_α (x, y) = (1 − y + α x, x)`, as a permutation of `k²`. -/
def u (α : k) : Equiv.Perm (k × k) where
  toFun p := (1 - p.2 + α * p.1, p.1)
  invFun p := (p.2, 1 - p.1 + α * p.2)
  left_inv p := Prod.ext rfl (show 1 - (1 - p.2 + α * p.1) + α * p.1 = p.2 by ring)
  right_inv p := Prod.ext (show 1 - (1 - p.1 + α * p.2) + α * p.2 = p.1 by ring) rfl

/-- a) ⇔ d): **Théorème (p. 112)**, `u_α^n = id ⇔ F_n(α) = 0`, over any commutative ring. -/
theorem zpow_eq_one_iff (α : k) (n : ℤ) : u α ^ n = 1 ↔ (F k n).eval α = 0 := by
  sorry

end Map

end Grothendieck.Folder78

end

-- From Challenge/Folder79.lean
@[expose] public section

namespace Grothendieck.Folder79

section RankTwo

open Matrix

variable {R : Type*} [CommRing R]

/-- `x ∧ y` in the basis of `R²`. -/
def det2 (x y : Fin 2 → R) : R := x 0 * y 1 - x 1 * y 0

omit [CommRing R] in
theorem vec_ext {x y : Fin 2 → R} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  funext i; fin_cases i <;> assumption

theorem mulVec_apply2 (M : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) (i : Fin 2) :
    (M *ᵥ x) i = M i 0 * x 0 + M i 1 * x 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem det2_mulVec (M : Matrix (Fin 2) (Fin 2) R) (x y : Fin 2 → R) :
    det2 (M *ᵥ x) (M *ᵥ y) = M.det * det2 x y := by
  simp only [det2, mulVec_apply2, Matrix.det_fin_two]; ring

/-- Coordinates in a basis `(x, y)` with `x ∧ y = 1`:
`z = (z ∧ y) x + (x ∧ z) y`. -/
theorem decomp {x y : Fin 2 → R} (h : det2 x y = 1) (z : Fin 2 → R) :
    z = det2 z y • x + det2 x z • y := by
  unfold det2 at h
  apply vec_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, det2]
  · linear_combination (-(z 0)) * h
  · linear_combination (-(z 1)) * h

/-- `x ∈ M*`: `x` is the first vector of a basis of `R²`. -/
def Unimod (x : Fin 2 → R) : Prop := ∃ y, det2 x y = 1

variable (R) in
/-- The relation `x = ± y` on `M*`. -/
def pmSetoid : Setoid {x : Fin 2 → R // Unimod x} where
  r x y := x.1 = y.1 ∨ x.1 = -y.1
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (by rw [h, neg_neg])),
    fun h1 h2 => by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> simp⟩

variable (R) in
/-- `S_M = M*/±1`, the vertices. -/
def Vtx := Quotient (pmSetoid R)

/-- The vertex of a vector `x` with `x ∧ y = 1`. -/
def vtx {x y : Fin 2 → R} (h : det2 x y = 1) : Vtx R := Quotient.mk _ ⟨x, y, h⟩

theorem vtx_eq_iff {x y x' y' : Fin 2 → R} (h : det2 x y = 1) (h' : det2 x' y' = 1) :
    vtx h = vtx h' ↔ x = x' ∨ x = -x' :=
  ⟨fun e => Quotient.exact e, fun e => Quotient.sound e⟩

/-- The action of `SL(2, R)` on `S_M`. -/
def act (g : Matrix.SpecialLinearGroup (Fin 2) R) : Vtx R → Vtx R :=
  Quotient.map (fun x => ⟨g.1 *ᵥ x.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨g.1 *ᵥ y, by rw [det2_mulVec, g.2, hy, one_mul]⟩⟩)
    (fun x y h => h.elim (fun h => Or.inl (by simp [h]))
      (fun h => Or.inr (by simp [h, Matrix.mulVec_neg])))

theorem det2_smul_left (c : R) (x y : Fin 2 → R) : det2 (c • x) y = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_smul_right (c : R) (x y : Fin 2 → R) : det2 x (c • y) = c * det2 x y := by
  simp only [det2, Pi.smul_apply, smul_eq_mul]; ring

theorem det2_add_left (x x' y : Fin 2 → R) : det2 (x + x') y = det2 x y + det2 x' y := by
  simp only [det2, Pi.add_apply]; ring

theorem det2_self (x : Fin 2 → R) : det2 x x = 0 := by unfold det2; ring

theorem det2_neg_left (x y : Fin 2 → R) : det2 (-x) y = -det2 x y := by
  simp only [det2, Pi.neg_apply]; ring

theorem det2_scal (c : Rˣ) {x y : Fin 2 → R} (h : det2 x y = 1) :
    det2 ((c : R) • x) ((↑c⁻¹ : R) • y) = 1 := by
  rw [det2_smul_left, det2_smul_right, h]; simp

/-- The scalar `c ∈ R*`, acting on `S_M`. -/
def scal (c : Rˣ) : Vtx R → Vtx R :=
  Quotient.map (fun x => ⟨(c : R) • x.1, by
      obtain ⟨y, hy⟩ := x.2
      exact ⟨(↑c⁻¹ : R) • y, det2_scal c hy⟩⟩)
    (fun x y h => h.elim (fun h => Or.inl (by simp [h]))
      (fun h => Or.inr (by simp [h])))

/-- The ideal `2R` is contained in `{0, 2}`. With `2 ≠ 0` this is `2R = {0, 2} ≠ {0}`. -/
def Exceptional (R : Type*) [CommRing R] : Prop := ∀ s : R, 2 * s = 0 ∨ 2 * s = 2

theorem Exceptional.four (hR : Exceptional R) : (4 : R) = 0 := by
  rcases hR 2 with h | h
  · linear_combination h
  · linear_combination 2 * h

/-- Independence of the partner: if `2R ⊂ {0, 2}`, `x ∧ y = 1`, `x' ∧ y' = 1`
and `x' = ± x`, then `x' + 2 y' = ± (x + 2 y)`. -/
theorem Exceptional.sigma_rel (hR : Exceptional R) {x y x' y' : Fin 2 → R}
    (h : det2 x y = 1) (h' : det2 x' y' = 1) (hx : x' = x ∨ x' = -x) :
    x' + (2 : R) • y' = x + (2 : R) • y ∨ x' + (2 : R) • y' = -(x + (2 : R) • y) := by
  have h4 := hR.four
  -- write `y'` in the basis `(x, y)`
  have hd := decomp h y'
  rcases hx with hx | hx <;> rw [hx] at h' ⊢
  · have hb : det2 x y' = 1 := h'
    rw [hb, one_smul] at hd
    rcases hR (det2 y' y) with h2 | h2
    · left; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (x i) * h2
    · right; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2 + (x i + y i) * h4
  · have hb : det2 x y' = -1 := by rw [← neg_neg x, det2_neg_left, h']
    rw [hb] at hd
    rcases hR (det2 y' y) with h2 | h2
    · right; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2
    · left; rw [hd]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (x i) * h2 - (y i) * h4

theorem det2_sigma {x y : Fin 2 → R} (h : det2 x y = 1) : det2 (x + (2 : R) • y) y = 1 := by
  rw [det2_add_left, det2_smul_left, det2_self, h]; ring

/-- The extra element `σ` of the commutant (pages 94 and 95), for `2R ⊂ {0, 2}`:
`ẋ ↦ (x + 2y)˙` for any `y` with `x ∧ y = 1`. In the basis `(e₁, e₂)` it sends
`ė₁` to the class of `(1, 2)`, the image of `e₁` by the matrix with rows
`(1, 0)` and `(2, 1)`. -/
noncomputable def sigma (hR : Exceptional R) : Vtx R → Vtx R :=
  Quotient.lift (fun x => vtx (det2_sigma x.2.choose_spec))
    (fun x x' hx => (vtx_eq_iff _ _).2 (hR.sigma_rel x'.2.choose_spec x.2.choose_spec hx))

/-- **Pages 92 to 95, the commutant.** A map of `S_M = M*/±1` to itself that
commutes with `SL(2, R)` is a scalar `c ∈ R*`, or, when `2R ⊂ {0, 2}`, a scalar
times `σ`. No hypothesis on `R`; the map need not be assumed bijective. -/
theorem commutant (f : Vtx R → Vtx R) (hf : ∀ g v, f (act g v) = act g (f v)) :
    (∃ c : Rˣ, f = scal c) ∨ (∃ hR : Exceptional R, ∃ c : Rˣ, f = scal c ∘ sigma hR) := by
  sorry

end RankTwo

end Grothendieck.Folder79

end

-- From Challenge/Folder80.lean
@[expose] public section

namespace Grothendieck.Folder80

/-- The determinant of three integer triples. -/
def det3 (u v w : Fin 3 → ℤ) : ℤ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Three lines (indices into an arrangement) are concurrent. -/
def Concurrent {n : ℕ} (L : Fin n → Fin 3 → ℤ) (i j k : Fin n) : Prop := det3 (L i) (L j) (L k) = 0

/-- Line `m` passes through the vertex `L i ∩ L j`. -/
def Through {n : ℕ} (L : Fin n → Fin 3 → ℤ) (m i j : Fin n) : Prop :=
  m = i ∨ m = j ∨ Concurrent L m i j

/-- The counterexample: `AB, BC, CA, a, b, c` (indices `0, …, 5`). -/
def six : Fin 6 → Fin 3 → ℤ :=
  ![![0, 1, 0], ![1, 1, -1], ![1, 0, 0], ![2, -1, 0], ![3, -1, -3], ![5, -1, 1]]

/-- **Not covered by two pencils**: no two vertices have every line through one of them. -/
theorem six_not_two_pencils :
    ¬ ∃ i j k l : Fin 6, i ≠ j ∧ k ≠ l ∧ ∀ m, Through six m i j ∨ Through six m k l := by
  sorry

end Grothendieck.Folder80

end

-- From Challenge/Folder80Maps1.lean
@[expose] public section

namespace Grothendieck.Folder80Maps1

open Filter Topology Matrix

section SignVectors

variable {E : Type*}

/-- `Z` is a face of `X` (conformal order): `Z e ∈ {0, X e}` for all `e`. -/
def Conf (Z X : E → SignType) : Prop := ∀ e, Z e = 0 ∨ Z e = X e

/-- The closed cell of `ℝP²` of the cell `±X`: the nonzero covectors `Z ≤ ±X`. -/
def PCl (L : Set (E → SignType)) (X : E → SignType) : Set (E → SignType) :=
  {Z | Z ∈ L ∧ Z ≠ 0 ∧ (Conf Z X ∨ Conf Z (-X))}

/-- The « cas latticiel »: two closed cells meet in nothing or in a single closed cell. -/
def Lattice (L : Set (E → SignType)) : Prop :=
  ∀ X ∈ L, ∀ Y ∈ L, X ≠ 0 → Y ≠ 0 →
    PCl L X ∩ PCl L Y = ∅ ∨ ∃ W ∈ L, W ≠ 0 ∧ PCl L X ∩ PCl L Y = PCl L W

variable {L : Set (E → SignType)}

end SignVectors

section Lines

variable {ι : Type*} (ℓ : ι → Fin 3 → ℝ)

/-- The sign vector of a point. -/
noncomputable def sgn (p : Fin 3 → ℝ) : ι → SignType := fun i => SignType.sign (ℓ i ⬝ᵥ p)

/-- The covectors of the arrangement. -/
def cov : Set (ι → SignType) := Set.range (sgn ℓ)

/-- Two points that carry every line between them, neither on all the lines: the arrangement
is covered by two pencils (types `I_N`, `I_{p,q}`, `II′_{p,q}`). -/
def TwoPencil : Prop :=
  ∃ p q : Fin 3 → ℝ, sgn ℓ p ≠ 0 ∧ sgn ℓ q ≠ 0 ∧ ∀ i, ℓ i ⬝ᵥ p = 0 ∨ ℓ i ⬝ᵥ q = 0

variable {ℓ}

/-- **The lattice criterion for lines.** The arrangement is latticial iff no two points carry
every line between them. -/
theorem lattice_iff_not_twoPencil [Fintype ι] : Lattice (cov ℓ) ↔ ¬ TwoPencil ℓ := by
  sorry

end Lines

end Grothendieck.Folder80Maps1

end

-- From Challenge/Folder80Maps2.lean
public section

/-!
# Advertised statement: the bigon-free dichotomy for combinatorial pseudoline arrangements

A combinatorial arrangement of pseudolines in the real projective plane is a generalised map
with flags labelled by lines (`PseudolineMap`). If no line carries fewer than three vertices
(`BigonFree`), the arrangement is four lines in general position (`IsII4`) or contains five
lines in general position, a pencil of three and a pencil of two in which none of these five lines joins the two centres, or the complete quadrangle.
-/

namespace Grothendieck.Folder80Maps2

section Core

variable {P L : Type*} (on : P → L → Prop)

/-- Three lines are concurrent. -/
def C (a b c : L) : Prop := ∃ p, on p a ∧ on p b ∧ on p c

/-- Four lines in general position: distinct, no three concurrent. -/
def GP4 (a b c d : L) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ¬C on a b c ∧ ¬C on a b d ∧ ¬C on a c d ∧ ¬C on b c d

/-- Five lines in general position: distinct, no three concurrent. -/
def GP5 (a b c d e : L) : Prop :=
  GP4 on a b c d ∧ a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e ∧
    ¬C on a b e ∧ ¬C on a c e ∧ ¬C on a d e ∧ ¬C on b c e ∧ ¬C on b d e ∧ ¬C on c d e

/-- Every line carries at least three vertices. -/
def BigonFree : Prop := ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- `II_4`: the arrangement is four lines in general position. -/
def IsII4 : Prop := ∃ a b c d, GP4 on a b c d ∧ ∀ m, m = a ∨ m = b ∨ m = c ∨ m = d

/-- `II_5`: five lines in general position. -/
def HasII5 : Prop := ∃ a b c d e, GP5 on a b c d e

/-- `II′_{3,2}`: `a, b, c` through `p`, `d, e` not through `p`, and their meeting point on none
of `a, b, c` (so, among these five lines, it is the only concurrent triple, and none of the five joins
the two centres; another line of the arrangement may join them). -/
def HasII32 : Prop :=
  ∃ a b c d e : L, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ ∃ p, on p a ∧ on p b ∧ on p c ∧ ¬on p d ∧
    ¬on p e ∧ ∀ q, on q d → on q e → ¬on q a ∧ ¬on q b ∧ ¬on q c

/-- No line of the arrangement passes through `p`, `q` and `r`. -/
def NC (p q r : P) : Prop := ∀ m, on p m → on q m → ¬on r m

/-- Some line of the arrangement passes through `p` and `q`. -/
def J (p q : P) : Prop := ∃ m, on p m ∧ on q m

/-- `III_6`, the complete quadrangle: four points, no three on a line, pairwise joined. -/
def HasIII6 : Prop :=
  ∃ p q r s : P, J on p q ∧ J on p r ∧ J on p s ∧ J on q r ∧ J on q s ∧ J on r s ∧
    NC on p q r ∧ NC on p q s ∧ NC on p r s ∧ NC on q r s

end Core

section Maps

open Relation


/-- A generalised map (a combinatorial map of a possibly non-orientable surface): flags with
three fixed-point-free involutions, `a0` and `a2` commuting with `a0 a2` fixed-point-free. -/
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d


namespace GMap

variable {D : Type*} (M : GMap D)

/-- Vertices are the classes of `⟨a1, a2⟩`. -/
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x
/-- Edges are the classes of `⟨a0, a2⟩`. -/
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x
/-- Faces are the classes of `⟨a0, a1⟩`. -/
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x

/-- The vertex of a flag. -/
def vtx (d : D) : M.Vtx := Quot.mk _ d
/-- The edge of a flag. -/
def edge (d : D) : M.Edge := Quot.mk _ d
/-- The face of a flag. -/
def face (d : D) : M.Face := Quot.mk _ d


/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face


end GMap

open GMap

/-- A combinatorial pseudoline arrangement (page 60): a generalised map with flags labelled by
lines, constant on edges; a line through a vertex has there the four flags of two edge-ends
(it passes once); each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; the surface is a projective plane, `χ = 1`. -/
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1

namespace PseudolineMap

variable {D L : Type*} (X : PseudolineMap D L)

/-- The line `l` passes through the vertex `v`. -/
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l

variable {X}

-- Finitely many flags: the Euler characteristic `χ = 1` is meaningful for finite maps.
variable [Fintype D]


/-- **The page's boxed statement** (pages 20, 24): every bigon-free combinatorial arrangement of
pseudolines in the real projective plane is `II_4` or contains `II_5`, `II′_{3,2}` or
`III_6`. -/
theorem map_dichotomy (hbf : BigonFree X.On) :
    IsII4 X.On ∨ HasII5 X.On ∨ HasII32 X.On ∨ HasIII6 X.On := by
  sorry

end PseudolineMap

end Maps

end Grothendieck.Folder80Maps2

end

-- From Challenge/Folder80Maps3.lean
@[expose] public section

namespace Grothendieck.Folder80Maps3

open Relation

/-- A set invariant under the generators of an equivalence closure is invariant under it. -/
theorem eqvGen_iff {α : Type*} {r : α → α → Prop} (S : α → Prop) (h : ∀ x y, r x y → (S x ↔ S y))
    {a b : α} (hab : EqvGen r a b) : S a ↔ S b :=
  (Equivalence.eqvGen_iff (r := fun x y => S x ↔ S y) ⟨fun _ => .rfl, .symm, .trans⟩).1
    (EqvGen.mono h _ _ hab)

/-- A generalised map: flags with three fixed-point-free involutions, `a0` and `a2` commuting
with `a0 a2` fixed-point-free. -/
structure GMap (D : Type*) where
  a0 : D → D
  a1 : D → D
  a2 : D → D
  a0_a0 : ∀ d, a0 (a0 d) = d
  a1_a1 : ∀ d, a1 (a1 d) = d
  a2_a2 : ∀ d, a2 (a2 d) = d
  a0_ne : ∀ d, a0 d ≠ d
  a1_ne : ∀ d, a1 d ≠ d
  a2_ne : ∀ d, a2 d ≠ d
  a0_a2 : ∀ d, a0 (a2 d) = a2 (a0 d)
  a02_ne : ∀ d, a0 (a2 d) ≠ d

namespace GMap

variable {D : Type*} (M : GMap D)

/-- Vertices are the classes of `⟨a1, a2⟩`. -/
def Vtx := Quot fun x y : D => y = M.a1 x ∨ y = M.a2 x

/-- Edges are the classes of `⟨a0, a2⟩`. -/
def Edge := Quot fun x y : D => y = M.a0 x ∨ y = M.a2 x

/-- Faces are the classes of `⟨a0, a1⟩`. -/
def Face := Quot fun x y : D => y = M.a0 x ∨ y = M.a1 x

/-- The vertex of a flag. -/
def vtx (d : D) : M.Vtx := Quot.mk _ d

/-- The edge of a flag. -/
def edge (d : D) : M.Edge := Quot.mk _ d

/-- The Euler characteristic `V − E + F`. -/
noncomputable def euler : ℤ := Nat.card M.Vtx - Nat.card M.Edge + Nat.card M.Face

variable {M}

@[simp] theorem vtx_a1 (d : D) : M.vtx (M.a1 d) = M.vtx d := (Quot.sound (.inl rfl)).symm

@[simp] theorem vtx_a2 (d : D) : M.vtx (M.a2 d) = M.vtx d := (Quot.sound (.inr rfl)).symm

@[simp] theorem edge_a0 (d : D) : M.edge (M.a0 d) = M.edge d := (Quot.sound (.inl rfl)).symm

@[simp] theorem edge_a2 (d : D) : M.edge (M.a2 d) = M.edge d := (Quot.sound (.inr rfl)).symm

theorem a0_eq_iff {x y : D} : M.a0 x = y ↔ x = M.a0 y :=
  ⟨fun h => h ▸ (M.a0_a0 x).symm, fun h => h ▸ M.a0_a0 y⟩

theorem a1_eq_iff {x y : D} : M.a1 x = y ↔ x = M.a1 y :=
  ⟨fun h => h ▸ (M.a1_a1 x).symm, fun h => h ▸ M.a1_a1 y⟩

theorem a2_eq_iff {x y : D} : M.a2 x = y ↔ x = M.a2 y :=
  ⟨fun h => h ▸ (M.a2_a2 x).symm, fun h => h ▸ M.a2_a2 y⟩

/-- An edge has exactly the four flags `d, a0 d, a2 d, a0 a2 d`. -/
theorem edge_eq {d e : D} :
    M.edge e = M.edge d ↔ e = d ∨ e = M.a0 d ∨ e = M.a2 d ∨ e = M.a0 (M.a2 d) := by
  constructor
  · intro h
    refine (eqvGen_iff (fun x => x = d ∨ x = M.a0 d ∨ x = M.a2 d ∨ x = M.a0 (M.a2 d)) ?_
      (Quot.eqvGen_exact h)).2 (.inl rfl)
    rintro x y (rfl | rfl)
    · simp only [a0_eq_iff, M.a0_a0]; tauto
    · simp only [a2_eq_iff, ← M.a0_a2, M.a2_a2]; tauto
  · rintro (rfl | rfl | rfl | rfl) <;> simp

theorem edge_four (d : D) : [d, M.a0 d, M.a2 d, M.a0 (M.a2 d)].Nodup := by
  have := M.a0_ne d; have := M.a2_ne d; have := M.a02_ne d; have := M.a0_ne (M.a2 d)
  simp_all [eq_comm, a0_eq_iff, M.a0_a0]

end GMap

open GMap

/-- Every line carries at least three vertices. -/
def BigonFree {P L : Type*} (on : P → L → Prop) : Prop :=
  ∀ l : L, ∃ p q r, on p l ∧ on q l ∧ on r l ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r

/-- A combinatorial pseudoline arrangement (page 60), as in `Folder80Maps2`: a generalised map
with flags labelled by lines, constant on edges; a line through a vertex has there the four
flags of two edge-ends; each line is connected; every vertex is on two lines; two lines meet at
exactly one vertex; `χ = 1`. -/
structure PseudolineMap (D L : Type*) where
  M : GMap D
  line : D → L
  line_a0 : ∀ d, line (M.a0 d) = line d
  line_a2 : ∀ d, line (M.a2 d) = line d
  pass : ∀ d, Nat.card {e // M.vtx e = M.vtx d ∧ line e = line d} = 4
  conn : ∀ d e, line d = line e →
    EqvGen (fun x y => y = M.a0 x ∨ (M.vtx y = M.vtx x ∧ line y = line x)) d e
  two : ∀ d, ∃ e, M.vtx e = M.vtx d ∧ line e ≠ line d
  meet : ∀ l l' : L, l ≠ l' →
    ∃! v, (∃ d, M.vtx d = v ∧ line d = l) ∧ (∃ d, M.vtx d = v ∧ line d = l')
  euler : M.euler = 1

namespace PseudolineMap

variable {D L : Type*} (X : PseudolineMap D L)

/-- The line `l` passes through the vertex `v`. -/
def On (v : X.M.Vtx) (l : L) : Prop := ∃ d, X.M.vtx d = v ∧ X.line d = l

variable {X}

/-- A line whose flags all sit at two vertices `u, w` is not bigon-free. -/
theorem confined (hbf : BigonFree X.On) {l : L} {u w : X.M.Vtx}
    (H : ∀ e, X.line e = l → X.M.vtx e = u ∨ X.M.vtx e = w) : False := by
  obtain ⟨p, q, r, ⟨d1, rfl, h1⟩, ⟨d2, rfl, h2⟩, ⟨d3, rfl, h3⟩, h12, h13, h23⟩ := hbf l
  rcases H _ h1 with h1 | h1 <;> rcases H _ h2 with h2 | h2 <;> rcases H _ h3 with h3 | h3 <;>
    simp_all

/-- The connected line `l` stays in a set of vertices stable under `a0` along `l`. -/
theorem confine {l : L} (Z : X.M.Vtx → Prop)
    (h : ∀ x, X.line x = l → Z (X.M.vtx x) → Z (X.M.vtx (X.M.a0 x))) {d : D} (hd : X.line d = l)
    (hZ : Z (X.M.vtx d)) {e : D} (he : X.line e = l) : Z (X.M.vtx e) := by
  refine (eqvGen_iff (fun x => X.line x = l → Z (X.M.vtx x)) ?_ (X.conn d e (hd.trans he.symm))).1
    (fun _ => hZ) he
  rintro x y (rfl | ⟨h1, h2⟩)
  · rw [X.line_a0]
    exact ⟨fun h' hx => h _ hx (h' hx), fun h' hx => by
      simpa [X.M.a0_a0] using h _ (by rwa [X.line_a0]) (h' hx)⟩
  · rw [h1, h2]

variable [Fintype D]

open Classical in
/-- The four flags of a line at a vertex. -/
theorem at_four {d x1 x2 x3 x4 : D} (hn : [x1, x2, x3, x4].Nodup)
    (hx : ∀ x ∈ [x1, x2, x3, x4], X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d) {f : D}
    (hf : X.M.vtx f = X.M.vtx d) (hl : X.line f = X.line d) : f ∈ [x1, x2, x3, x4] := by
  have h4 := X.pass d
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have := Finset.eq_of_subset_of_card_le (s := [x1, x2, x3, x4].toFinset)
    (t := Finset.univ.filter fun e => X.M.vtx e = X.M.vtx d ∧ X.line e = X.line d)
    (fun x hx' => by simpa using hx _ (List.mem_toFinset.1 hx'))
    (by rw [h4, List.toFinset_card_of_nodup hn]; rfl)
  simpa [hf, hl] using (Finset.ext_iff.1 this f).2

/-- No loop: the two ends of an edge are distinct vertices. -/
theorem noLoop (hbf : BigonFree X.On) (d : D) : X.M.vtx (X.M.a0 d) ≠ X.M.vtx d := by
  intro h
  have hall : ∀ x ∈ [d, X.M.a0 d, X.M.a2 d, X.M.a0 (X.M.a2 d)],
      X.M.vtx x = X.M.vtx d ∧ X.line x = X.line d := by
    simp [h, X.line_a0, X.line_a2, X.M.a0_a2]
  refine confined hbf (l := X.line d) (u := X.M.vtx d) (w := X.M.vtx d) fun e he => .inl ?_
  refine confine (fun t => t = X.M.vtx d) (fun x hx hxv => ?_) rfl rfl he
  have := at_four (edge_four d) hall hxv hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> simp [h, X.M.a0_a0, X.M.a0_a2]

/-- At a vertex, the two flags of an edge-end are followed by flags of two different edges. -/
theorem edge_a1_a2_ne (hbf : BigonFree X.On) (u : D) :
    X.M.edge (X.M.a1 (X.M.a2 u)) ≠ X.M.edge (X.M.a1 u) := by
  intro e1
  have hn := noLoop hbf
  rcases edge_eq.1 e1 with k | k | k | k
  · exact X.M.a2_ne u (by simpa [X.M.a1_a1] using congrArg X.M.a1 k)
  · exact hn (X.M.a1 u) (by rw [← k]; simp)
  · -- `a1 a2 u = a2 a1 u`: the vertex of `u` has four flags only
    obtain ⟨e, hev, hel⟩ := X.two u
    have hS : ∀ x, X.M.vtx x = X.M.vtx u →
        x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨ x = X.M.a1 (X.M.a2 u) := fun x hx => by
      refine (eqvGen_iff (fun x => x = u ∨ x = X.M.a1 u ∨ x = X.M.a2 u ∨
        x = X.M.a1 (X.M.a2 u)) ?_ (Quot.eqvGen_exact hx)).2 (.inl rfl)
      have k' : X.M.a2 (X.M.a1 (X.M.a2 u)) = X.M.a1 u := by rw [k, X.M.a2_a2]
      rintro x y (rfl | rfl)
      · simp only [a1_eq_iff, X.M.a1_a1]; tauto
      · simp only [a2_eq_iff, ← k, k', X.M.a2_a2]; tauto
    have hl1 : X.line (X.M.a1 u) ≠ X.line u := fun hl => hel <| by
      rcases hS e hev with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    classical
    have h4 := X.pass u
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
    have hsub : (Finset.univ.filter fun e => X.M.vtx e = X.M.vtx u ∧ X.line e = X.line u) ⊆
        {u, X.M.a2 u} := fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hS x hx.1 with rfl | rfl | rfl | rfl <;> simp_all [X.line_a2]
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  · exact hn (X.M.a2 (X.M.a1 u)) (by rw [← k]; simp)

section Chains

open Matrix

variable (X) in
/-- The vertex `v` is an end of the edge `e`. -/
def Inc (v : X.M.Vtx) (e : X.M.Edge) : Prop := ∃ d, X.M.vtx d = v ∧ X.M.edge d = e

variable (X) in
/-- The line of an edge. -/
def lineE : X.M.Edge → L :=
  Quot.lift X.line fun x _ h => h.elim (fun h => h ▸ (X.line_a0 x).symm) fun h =>
    h ▸ (X.line_a2 x).symm

omit [Fintype D] in
@[simp] theorem lineE_edge (d : D) : X.lineE (X.M.edge d) = X.line d := rfl

/-- The flags at a vertex on a given edge are `d` and `a2 d`. -/
theorem at_edge (hbf : BigonFree X.On) {d x : D} :
    X.M.vtx x = X.M.vtx d ∧ X.M.edge x = X.M.edge d ↔ x = d ∨ x = X.M.a2 d := by
  refine ⟨fun ⟨hv, he⟩ => ?_, by rintro (rfl | rfl) <;> simp⟩
  rcases edge_eq.1 he with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact (noLoop hbf _ hv).elim
  · exact .inr rfl
  · exact (noLoop hbf (X.M.a2 d) (by rw [hv, vtx_a2])).elim

omit [Fintype D] in
theorem inc_iff (d : D) (v : X.M.Vtx) :
    X.Inc v (X.M.edge d) ↔ v = X.M.vtx d ∨ v = X.M.vtx (X.M.a0 d) := by
  constructor
  · rintro ⟨x, rfl, hx⟩
    rcases edge_eq.1 hx with rfl | rfl | rfl | rfl <;> simp [X.M.a0_a2]
  · rintro (rfl | rfl)
    exacts [⟨d, rfl, rfl⟩, ⟨_, rfl, edge_a0 d⟩]

end Chains

variable (X) in
/-- The rotation `φ = a2 a1` around a vertex: from an edge-end to the next one. -/
def phi : Equiv.Perm D :=
  Function.Involutive.toPerm X.M.a2 X.M.a2_a2 * Function.Involutive.toPerm X.M.a1 X.M.a1_a1

omit [Fintype D] in
theorem phi_apply (x : D) : X.phi x = X.M.a2 (X.M.a1 x) := rfl

omit [Fintype D] in
theorem phi_inv_apply (x : D) : X.phi⁻¹ x = X.M.a1 (X.M.a2 x) :=
  (Equiv.Perm.inv_eq_iff_eq).2 (by simp [phi_apply, X.M.a1_a1, X.M.a2_a2])

omit [Fintype D] in
theorem a2_phi (x : D) : X.M.a2 (X.phi x) = X.M.a1 x := X.M.a2_a2 _

omit [Fintype D] in
/-- A function invariant under `φ` is invariant under its powers. -/
theorem zpow_inv {α : Type*} (g : D → α) (h : ∀ x, g (X.phi x) = g x) (k : ℤ) (x : D) :
    g ((X.phi ^ k) x) = g x := by
  induction k with
  | zero => simp
  | succ n ih => rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, h, ih]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, ← ih,
      ← h (X.phi⁻¹ _)]
    exact congrArg g ((Equiv.eq_symm_apply X.phi).mp rfl)

omit [Fintype D] in
@[simp] theorem vtx_phi1 (x : D) : X.M.vtx (X.phi x) = X.M.vtx x := by simp [phi_apply]

omit [Fintype D] in
@[simp] theorem vtx_phi (k : ℤ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x :=
  zpow_inv _ (fun x => by simp [phi_apply]) k x

omit [Fintype D] in
@[simp] theorem vtx_phi' (k : ℕ) (x : D) : X.M.vtx ((X.phi ^ k) x) = X.M.vtx x := by
  simpa using vtx_phi (X := X) k x

omit [Fintype D] in
/-- `a2 φ^k = φ^{-k} a2`. -/
theorem a2_zpow (k : ℤ) (x : D) : X.M.a2 ((X.phi ^ k) x) = (X.phi ^ (-k)) (X.M.a2 x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_one_add, Equiv.Perm.mul_apply, a2_phi,
      show -(1 + (n : ℤ)) = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, ← ih, zpow_neg_one,
      phi_inv_apply, X.M.a2_a2]
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, Equiv.Perm.mul_apply, zpow_neg_one,
      phi_inv_apply, ← phi_apply, ih, ← Equiv.Perm.mul_apply, ← zpow_one_add]
    congr 2; ring

omit [Fintype D] in
/-- The two orbits of `φ` at a vertex are exchanged by `a2`: `a2 φ^i x ≠ φ^j x`. -/
theorem a2_ne_zpow (i j : ℤ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  intro h
  rw [a2_zpow] at h
  have h' : X.M.a2 x = (X.phi ^ (i + j)) x := by
    have := congrArg (X.phi ^ i) h
    rwa [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply,
      ← Equiv.Perm.mul_apply, ← zpow_add] at this
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' (i + j)
  · apply X.M.a2_ne ((X.phi ^ t) x)
    rw [a2_zpow, h', ht, ← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2; ring
  · apply X.M.a1_ne ((X.phi ^ t) x)
    rw [← a2_phi, ← Equiv.Perm.mul_apply, ← zpow_one_add, a2_zpow, h', ht, ← Equiv.Perm.mul_apply,
      ← zpow_add]
    congr 2; ring

omit [Fintype D] in
/-- The flags at the vertex of `x` are the `φ^k x` and the `a2 φ^k x`. -/
theorem vtx_orbit {x y : D} (h : X.M.vtx y = X.M.vtx x) :
    ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x) := by
  let S : D → Prop := fun y => ∃ k : ℤ, y = (X.phi ^ k) x ∨ y = X.M.a2 ((X.phi ^ k) x)
  have c1 : ∀ u, S u → S (X.M.a1 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨1 + k, .inr (by rw [zpow_one_add, Equiv.Perm.mul_apply, a2_phi])⟩
    · exact ⟨-1 + k, .inl (by rw [zpow_add, Equiv.Perm.mul_apply, zpow_neg_one, phi_inv_apply])⟩
  have c2 : ∀ u, S u → S (X.M.a2 u) := by
    rintro u ⟨k, rfl | rfl⟩
    · exact ⟨k, .inr rfl⟩
    · exact ⟨k, .inl (X.M.a2_a2 _)⟩
  refine (eqvGen_iff S ?_ (Quot.eqvGen_exact h)).2 ⟨0, .inl rfl⟩
  rintro u w (rfl | rfl)
  · exact ⟨c1 u, fun h => by simpa [X.M.a1_a1] using c1 _ h⟩
  · exact ⟨c2 u, fun h => by simpa [X.M.a2_a2] using c2 _ h⟩

open Classical in
variable (X) in
/-- The number `ν(v)` of lines through a vertex. -/
noncomputable def nu (v : X.M.Vtx) : ℕ :=
  ((Finset.univ.filter fun d => X.M.vtx d = v).image X.line).card

variable (X) in
/-- **Going straight** (page 60; (22) of page 41): half a turn around a vertex of `ν` lines,
`ν` edge-ends further, one finds the same line. -/
def Straight : Prop := ∀ d, X.line ((X.phi ^ X.nu (X.M.vtx d)) d) = X.line d

open Classical in
theorem card_vtx (x : D) :
    (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x).card = 4 * X.nu (X.M.vtx x) := by
  rw [Finset.card_eq_sum_card_image X.line, nu, Finset.sum_const_nat (m := 4), mul_comm]
  intro l hl
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hl
  have h4 := X.pass e
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  rw [Finset.filter_filter, ← h4]
  congr 1; ext a; simp [(Finset.mem_filter.1 he).2]

open Classical in
/-- A period of `φ` at a flag is at least the number `2ν` of edge-ends. -/
theorem four_nu_le (x : D) {q : ℕ} (hq : 0 < q) (h : (X.phi ^ q) x = x) :
    4 * X.nu (X.M.vtx x) ≤ 2 * q := by
  rw [← card_vtx]
  have hsub : (Finset.univ.filter fun d => X.M.vtx d = X.M.vtx x) ⊆
      ((Finset.range q) ×ˢ (Finset.univ : Finset Bool)).image
        fun p => if p.2 then X.M.a2 ((X.phi ^ p.1) x) else (X.phi ^ p.1) x := by
    intro y hy
    obtain ⟨k, hk⟩ := vtx_orbit (Finset.mem_filter.1 hy).2
    have hr : (X.phi ^ k) x = (X.phi ^ (k % q).toNat) x := by
      have h' : ((X.phi ^ (q : ℤ)) ^ (k / q)) x = x :=
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (by simpa using h) _
      conv_lhs => rw [← Int.emod_add_mul_ediv k q, zpow_add, Equiv.Perm.mul_apply, zpow_mul, h']
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    have hlt : (k % q).toNat < q := by
      have := Int.emod_lt_of_pos k (by omega : (0 : ℤ) < q); omega
    rcases hk with rfl | rfl
    exacts [Finset.mem_image.2 ⟨((k % q).toNat, false), by simp [hlt], by simp [hr]⟩,
      Finset.mem_image.2 ⟨((k % q).toNat, true), by simp [hlt], by simp [hr]⟩]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [mul_comm]

omit [Fintype D] in
theorem a2_ne_pow (i j : ℕ) (x : D) : X.M.a2 ((X.phi ^ i) x) ≠ (X.phi ^ j) x := by
  simpa using a2_ne_zpow (X := X) i j x

/-- Distinct powers below `2ν` of `φ` move a flag to distinct flags. -/
theorem pow_ne (y : D) {a b : ℕ} (hab : a < b) (hb : b < 2 * X.nu (X.M.vtx y)) :
    (X.phi ^ a) y ≠ (X.phi ^ b) y := fun h => by
  have := four_nu_le ((X.phi ^ a) y) (q := b - a) (by omega) (by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hab.le, ← h])
  rw [vtx_phi'] at this
  omega

theorem straight_pow (hs : X.Straight) (y : D) (i : ℕ) :
    X.line ((X.phi ^ (i + X.nu (X.M.vtx y))) y) = X.line ((X.phi ^ i) y) := by
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]
  simpa using hs ((X.phi ^ i) y)

open Classical in
/-- The `ν` edge-ends met in half a turn around a vertex carry distinct lines. -/
theorem line_inj (hs : X.Straight) (y : D) {i j : ℕ} (hij : i < j)
    (hj : j < X.nu (X.M.vtx y)) : X.line ((X.phi ^ i) y) ≠ X.line ((X.phi ^ j) y) := by
  intro hl
  set ν := X.nu (X.M.vtx y)
  have hn : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].Nodup := by
    have p : ∀ {a b : ℕ}, a < b → b < 2 * ν → (X.phi ^ a) y ≠ (X.phi ^ b) y :=
      fun h h' => pow_ne y h h'
    have q := a2_ne_pow (X := X)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨p hij (by omega), p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i i y h.symm⟩, ⟨p (by omega) (by omega), p (by omega) (by omega),
      fun h => q i j y h.symm⟩, ⟨p (by omega) (by omega), fun h => q i _ y h.symm⟩,
      fun h => q i _ y h.symm⟩
  have h4 := X.pass ((X.phi ^ i) y)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h4
  have hsub : [(X.phi ^ i) y, (X.phi ^ j) y, (X.phi ^ (i + ν)) y, (X.phi ^ (j + ν)) y,
      X.M.a2 ((X.phi ^ i) y)].toFinset ⊆ Finset.univ.filter fun e =>
        X.M.vtx e = X.M.vtx ((X.phi ^ i) y) ∧ X.line e = X.line ((X.phi ^ i) y) := by
    intro e he
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [ν, hl, X.line_a2, straight_pow hs y i, straight_pow hs y j]
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, h4] at this
  simp at this

section Parity

open Matrix

omit [Fintype D] in
theorem on_of_inc {w : X.M.Vtx} {e : X.M.Edge} (h : X.Inc w e) : X.On w (X.lineE e) := by
  obtain ⟨d, rfl, rfl⟩ := h; exact ⟨d, rfl, rfl⟩

omit [Fintype D] in
theorem meet_eq {l l' : L} (h : l ≠ l') {v w : X.M.Vtx} (hv : X.On v l) (hv' : X.On v l')
    (hw : X.On w l) (hw' : X.On w l') : v = w := by
  obtain ⟨u, -, hu⟩ := X.meet l l' h
  exact (hu v ⟨hv, hv'⟩).trans (hu w ⟨hw, hw'⟩).symm

end Parity

section Lift

/-- Two edge-ends adjacent around a vertex lie on different lines. -/
theorem line_a1_ne (hs : X.Straight) (d : D) : X.line (X.M.a1 d) ≠ X.line d := by
  classical
  obtain ⟨e, he, hl⟩ := X.two d
  have h2 : 1 < X.nu (X.M.vtx d) := Finset.one_lt_card.2 ⟨_, Finset.mem_image.2 ⟨d, by simp, rfl⟩,
    _, Finset.mem_image.2 ⟨e, by simp [he], rfl⟩, Ne.symm hl⟩
  exact fun h => line_inj hs d zero_lt_one h2 (by simpa [phi_apply, X.line_a2] using h.symm)

variable (X) in
/-- `e1, e, e2` are three consecutive sides of a face: the corner `(e1, e)` at one end of `e`
continued along `e` to the corner `(e, e2)` on the same side. These paths are the generalised
rotation system (19)–(21) of page 41. -/
def Path3 (e1 e e2 : X.M.Edge) : Prop :=
  ∃ d, X.M.edge (X.M.a1 d) = e1 ∧ X.M.edge d = e ∧ X.M.edge (X.M.a1 (X.M.a0 d)) = e2

variable {D' L' : Type*} [Fintype D'] {X' : PseudolineMap D' L'}

variable (X X') in
/-- An isomorphism of the skeletons decomposed into lines: bijections of vertices, edges and
lines preserving incidence and the line of each edge (the arrangements of dimension `1` of
page 40). -/
structure SkelIso where
  fV : X.M.Vtx ≃ X'.M.Vtx
  fE : X.M.Edge ≃ X'.M.Edge
  fL : L ≃ L'
  inc : ∀ v e, X.Inc v e ↔ X'.Inc (fV v) (fE e)
  line : ∀ e, X'.lineE (fE e) = fL (X.lineE e)

/-- The inverse isomorphism of skeletons. -/
def SkelIso.symm (f : SkelIso X X') : SkelIso X' X where
  fV := f.fV.symm
  fE := f.fE.symm
  fL := f.fL.symm
  inc v e := by rw [f.inc]; simp
  line e := by rw [Equiv.eq_symm_apply, ← f.line]; simp

/-- A flag is determined by its vertex, its edge and the edge after it. -/
theorem dart_unique (hbf : BigonFree X.On) {y y' : D} (hv : X.M.vtx y' = X.M.vtx y)
    (he : X.M.edge y' = X.M.edge y) (h1 : X.M.edge (X.M.a1 y') = X.M.edge (X.M.a1 y)) :
    y' = y := by
  rcases (at_edge hbf).1 ⟨hv, he⟩ with h | rfl
  · exact h
  · exact (edge_a1_a2_ne hbf y h1).elim

omit [Fintype D'] in
theorem exists_dart (hbf : BigonFree X.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) (d : D) :
    ∃ d', X'.M.vtx d' = f.fV (X.M.vtx d) ∧ X'.M.edge d' = f.fE (X.M.edge d) ∧
      X'.M.edge (X'.M.a1 d') = f.fE (X.M.edge (X.M.a1 d)) ∧
      X'.M.edge (X'.M.a1 (X'.M.a0 d')) = f.fE (X.M.edge (X.M.a1 (X.M.a0 d))) := by
  obtain ⟨d', h1, h2, h3⟩ := hT _ _ _ ⟨d, rfl, rfl, rfl⟩
  refine ⟨d', ?_, h2, h1, h3⟩
  have iv := (f.inc _ _).1 (⟨d, rfl, rfl⟩ : X.Inc (X.M.vtx d) (X.M.edge d))
  have iw := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
  rw [← h2, inc_iff] at iv iw
  have hvw : f.fV (X.M.vtx d) ≠ f.fV (X.M.vtx (X.M.a0 d)) := fun h => noLoop hbf d (f.fV.injective h).symm
  by_contra hne
  have hw : X'.M.vtx d' = f.fV (X.M.vtx (X.M.a0 d)) :=
    (iw.resolve_right fun h' => hvw ((iv.resolve_left fun h => hne h.symm).trans h'.symm)).symm
  -- the edge after `d` would join both ends of `d`, on another line
  have : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge (X.M.a1 d)) := by
    rw [f.inc, ← h1, ← hw]; exact ⟨_, vtx_a1 d', rfl⟩
  exact noLoop hbf d (meet_eq (line_a1_ne hs d) (lineE_edge (X := X) (X.M.a1 d) ▸ on_of_inc this)
    ⟨_, rfl, X.line_a0 d⟩ ⟨_, vtx_a1 d, rfl⟩ ⟨d, rfl, rfl⟩)

/-- **The general theorem on maps, page 41.** An isomorphism of decomposed skeletons that
carries the three-edge face paths to face paths is induced by a morphism of the arrangements
(commuting with `a0, a1, a2`, over the given bijections). -/
theorem lift (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight) (f : SkelIso X X')
    (hT : ∀ e1 e e2, X.Path3 e1 e e2 → X'.Path3 (f.fE e1) (f.fE e) (f.fE e2)) :
    ∃ g : D → D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      (∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ∧ ∀ d, X'.line (g d) = f.fL (X.line d) := by
  choose g hv he h1 h3 using exists_dart hbf hs f hT
  have hv' : ∀ d, X'.M.vtx (X'.M.a0 (g d)) = f.fV (X.M.vtx (X.M.a0 d)) := fun d => by
    have := (f.inc _ _).1 (⟨_, rfl, edge_a0 d⟩ : X.Inc (X.M.vtx (X.M.a0 d)) (X.M.edge d))
    rw [← he, inc_iff] at this
    exact (this.resolve_left fun h => noLoop hbf d (f.fV.injective (h.trans (hv d)))).symm
  refine ⟨g, fun d => ?_, fun d => ?_, fun d => ?_, hv, he, fun d => ?_⟩
  · exact dart_unique hbf' (by rw [hv, hv']) (by simp [he]) (by rw [h1, h3])
  · exact dart_unique hbf' (by simp [hv]) (by rw [he, h1]) (by rw [h1, X.M.a1_a1, X'.M.a1_a1, he])
  · exact ((at_edge hbf').1 (⟨by simp [hv], by simp [he]⟩ :
      X'.M.vtx (g (X.M.a2 d)) = X'.M.vtx (g d) ∧ X'.M.edge (g (X.M.a2 d)) = X'.M.edge (g d))
      ).resolve_left fun h => edge_a1_a2_ne hbf d (f.fE.injective (by rw [← h1, ← h1, h]))
  · rw [← lineE_edge, he, f.line]; rfl

/-- **Fullness reduces to face paths.** An isomorphism of decomposed skeletons of two bigon-free
arrangements comes from an isomorphism of the arrangements (a bijection of flags commuting with
`a0, a1, a2`) iff it preserves the three-edge face paths in both directions; the isomorphism is
then unique (`faithful`). -/
theorem lift_iff (hbf : BigonFree X.On) (hbf' : BigonFree X'.On) (hs : X.Straight)
    (hs' : X'.Straight) (f : SkelIso X X') :
    (∃ g : D ≃ D', (∀ d, g (X.M.a0 d) = X'.M.a0 (g d)) ∧ (∀ d, g (X.M.a1 d) = X'.M.a1 (g d)) ∧
      (∀ d, g (X.M.a2 d) = X'.M.a2 (g d)) ∧ (∀ d, X'.M.vtx (g d) = f.fV (X.M.vtx d)) ∧
      ∀ d, X'.M.edge (g d) = f.fE (X.M.edge d)) ↔
    ∀ e1 e e2, X.Path3 e1 e e2 ↔ X'.Path3 (f.fE e1) (f.fE e) (f.fE e2) := by
  sorry

end Lift

end PseudolineMap

end Grothendieck.Folder80Maps3

end

-- From Challenge/Folder80Signs.lean
@[expose] public section

namespace Grothendieck.Folder80Signs

open Grothendieck.Folder80Maps3 (BigonFree)

variable {P L : Type*} (on : P → L → Prop)

/-- Three pairwise distinct lines without a common point. -/
def Basis (i j l : L) : Prop :=
  i ≠ j ∧ i ≠ l ∧ j ≠ l ∧ ¬∃ p, on p i ∧ on p j ∧ on p l

/-- Two distinct lines meet in exactly one point, and every point is on two lines. -/
structure Incidence : Prop where
  meet : ∀ l l' : L, l ≠ l' → ∃ p, on p l ∧ on p l'
  unique : ∀ {l l' : L} {p q : P}, l ≠ l' → on p l → on p l' → on q l → on q l' → p = q
  two : ∀ {p : P} {l : L}, on p l → ∃ l', l' ≠ l ∧ on p l'

variable {on}

/-- The two chirotopes have the same separation relation along every line: what an isomorphism
of labelled skeleta gives, the cyclic order of the vertices along `i` being kept up to
reversal. -/
def SameSeparation (χ χ' : L → L → L → ZMod 2) (σ : L → L) : Prop :=
  ∀ i j k l m, Basis on i j l → Basis on i j m → Basis on i k l → Basis on i k m →
    χ' (σ i) (σ j) (σ l) + χ' (σ i) (σ j) (σ m) + χ' (σ i) (σ k) (σ l) + χ' (σ i) (σ k) (σ m) =
      χ i j l + χ i j m + χ i k l + χ i k m

/-- **Steps 1–4, from the cyclic orders to the reorientation.** In a bigon-free incidence
structure, two alternating chirotopes with the same separation relation along every line differ
by a reorientation. Only Folkman–Lawrence, from the reorientation to a homeomorphism, and the
reading of the separation relation on an actual arrangement, are left outside. -/
theorem reorientation_of_sameSeparation (hI : Incidence on) (hbf : BigonFree on)
    {χ χ' : L → L → L → ZMod 2} {σ : L → L}
    (a12 : ∀ i j l, χ j i l = χ i j l + 1) (a23 : ∀ i j l, χ i l j = χ i j l + 1)
    (a12' : ∀ i j l, χ' j i l = χ' i j l + 1) (a23' : ∀ i j l, χ' i l j = χ' i j l + 1)
    (H : SameSeparation (on := on) χ χ' σ) :
    ∃ r : L → ZMod 2, ∀ i j l, Basis on i j l →
      χ' (σ i) (σ j) (σ l) = χ i j l + r i + r j + r l := by
  sorry

end Grothendieck.Folder80Signs

end

-- From Challenge/Folder82.lean
@[expose] public section

open Matrix

namespace Folder82

variable {R : Type*} [CommRing R]

/-- `xX̃ + yỸ + zH̃` with `X̃ = E₁₂`, `Ỹ = E₂₁`, `H̃ = diag(1, −1)`. -/
def coord (x y z : R) : Matrix (Fin 2) (Fin 2) R := !![z, x; y, -z]

open LieAlgebra.SpecialLinear in
/-- `sl(2)` over `R`. -/
abbrev Sl2 (R : Type*) [CommRing R] := sl (Fin 2) R

/-- The element `xX̃ + yỸ + zH̃` of `sl(2)`. -/
def slMk (x y z : R) : Sl2 R :=
  ⟨coord x y z, by simp [LieAlgebra.SpecialLinear.sl, coord, trace_fin_two]⟩

@[simp] theorem slMk_val (x y z : R) : (slMk x y z).val = coord x y z := rfl

theorem slMk_eta (u : Sl2 R) : u = slMk (u.val 0 1) (u.val 1 0) (u.val 0 0) := by
  have h : u.val.trace = 0 := u.2
  rw [trace_fin_two] at h
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; linear_combination h

theorem slMk_add (x y z x' y' z' : R) :
    slMk x y z + slMk x' y' z' = slMk (x + x') (y + y') (z + z') := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]; ring

theorem slMk_smul (c x y z : R) : c • slMk x y z = slMk (c * x) (c * y) (c * z) := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]

/-- In characteristic 2, `sl(2)` is the Heisenberg algebra: `[u, u'] = (xy' − yx') H̃`. -/
theorem lie_slMk (h2 : (2 : R) = 0) (x y z x' y' z' : R) :
    ⁅slMk x y z, slMk x' y' z'⁆ = slMk 0 0 (x * y' - y * x') := by
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.sl_bracket]
  ext i j; fin_cases i <;> fin_cases j <;> simp [coord]
  · ring
  · linear_combination (z * x' - x * z') * h2
  · linear_combination (y * z' - z * y') * h2
  · ring

/-- The Lie endomorphism `xX̃ + yỸ + zH̃ ↦ g(x, y) + (ax + by + det g · z) H̃`, for a `2 × 2`
matrix `g` and `a, b ∈ R`: the pair `(g, (a, b))` of `GL(V) ⋉ Hom(V, det V)`. -/
def autFun (h2 : (2 : R) = 0) (g : Matrix (Fin 2) (Fin 2) R) (a b : R) : Sl2 R →ₗ⁅R⁆ Sl2 R where
  toFun u := slMk (g 0 0 * u.val 0 1 + g 0 1 * u.val 1 0) (g 1 0 * u.val 0 1 + g 1 1 * u.val 1 0)
    (a * u.val 0 1 + b * u.val 1 0 + g.det * u.val 0 0)
  map_add' u v := by
    rw [slMk_add]; congr 1 <;> simp <;> ring
  map_smul' c u := by
    rw [RingHom.id_apply, slMk_smul]; congr 1 <;> simp <;> ring
  map_lie' {u v} := by
    conv_lhs => rw [slMk_eta u, slMk_eta v, lie_slMk h2]
    rw [lie_slMk h2]
    simp only [slMk_val, coord, of_apply, cons_val', cons_val_zero, cons_val_one,
      empty_val', cons_val_fin_one, det_fin_two]
    congr 1 <;> ring

/-- **Automorphisms of `sl(2)` in characteristic 2**: a Lie endomorphism is bijective iff it is
`autFun g a b` with `det g` a unit, the parameters being unique. So `Aut(sl(2))(R)` is
`GL₂(R) ⋉ R²` (`autFun_comp`), the automorphisms of the split pair `(V, E)`, `E` an extension
of `V` by `det V`: an affine group of dimension 6. -/
theorem bijective_iff (h2 : (2 : R) = 0) (φ : Sl2 R →ₗ⁅R⁆ Sl2 R) :
    Function.Bijective φ ↔ ∃ (g : Matrix (Fin 2) (Fin 2) R) (a b : R),
      IsUnit g.det ∧ φ = autFun h2 g a b := by
  sorry

end Folder82

end

-- From Challenge/Folder83.lean
@[expose] public section

namespace Grothendieck.Folder83

open Polynomial TensorProduct

section Line

variable {k : Type*} [CommRing k]

/-- An element `x₀ + x₁u + x₂v + x₃uv` of `P = H ⊗ H'`, in the basis
`(1, u, v, uv)`. -/
@[ext] structure P (k : Type*) where
  x0 : k
  x1 : k
  x2 : k
  x3 : k

namespace P

instance : Add (P k) := ⟨fun x y => ⟨x.x0 + y.x0, x.x1 + y.x1, x.x2 + y.x2, x.x3 + y.x3⟩⟩

instance : SMul k (P k) := ⟨fun a x => ⟨a * x.x0, a * x.x1, a * x.x2, a * x.x3⟩⟩

@[simp] lemma add_x0 (x y : P k) : (x + y).x0 = x.x0 + y.x0 := rfl

@[simp] lemma add_x1 (x y : P k) : (x + y).x1 = x.x1 + y.x1 := rfl

@[simp] lemma add_x2 (x y : P k) : (x + y).x2 = x.x2 + y.x2 := rfl

@[simp] lemma add_x3 (x y : P k) : (x + y).x3 = x.x3 + y.x3 := rfl

@[simp] lemma smul_x0 (a : k) (x : P k) : (a • x).x0 = a * x.x0 := rfl

@[simp] lemma smul_x1 (a : k) (x : P k) : (a • x).x1 = a * x.x1 := rfl

@[simp] lemma smul_x2 (a : k) (x : P k) : (a • x).x2 = a * x.x2 := rfl

@[simp] lemma smul_x3 (a : k) (x : P k) : (a • x).x3 = a * x.x3 := rfl

/-- The basis vectors `1`, `u`, `v`, `uv`. -/
def one : P k := ⟨1, 0, 0, 0⟩

end P

open P

/-- The multiplication of `M(b, c; b', c'; t)` (table of page 92, left factor in
the row): `u² = bu − c`, `vu = (t − bb') + b'u + bv − uv`, `v(uv) = −bc' + c'u + tv`,
`(uv)u = −b'c + tu + cv`, `(uv)² = −cc' + t·uv`, and so on. -/
def mulM (b c b' c' t : k) (x y : P k) : P k where
  x0 := x.x0 * y.x0 - c * x.x1 * y.x1 - c' * x.x2 * y.x2 - c * c' * x.x3 * y.x3
    + (t - b * b') * x.x2 * y.x1 - b * c' * x.x2 * y.x3 - b' * c * x.x3 * y.x1
  x1 := x.x0 * y.x1 + x.x1 * y.x0 + b * x.x1 * y.x1 + b' * x.x2 * y.x1
    + c' * x.x2 * y.x3 - c' * x.x3 * y.x2 + t * x.x3 * y.x1
  x2 := x.x0 * y.x2 + x.x2 * y.x0 + b * x.x2 * y.x1 + b' * x.x2 * y.x2
    - c * x.x1 * y.x3 + c * x.x3 * y.x1 + t * x.x2 * y.x3
  x3 := x.x0 * y.x3 + x.x3 * y.x0 + b * x.x1 * y.x3 + b' * x.x3 * y.x2
    + t * x.x3 * y.x3 + x.x1 * y.x2 - x.x2 * y.x1

variable (b c b' c' t : k)

theorem one_mulM (x : P k) : mulM b c b' c' t one x = x := by
  ext <;> simp [mulM, one]

theorem mulM_one (x : P k) : mulM b c b' c' t x one = x := by
  ext <;> simp [mulM, one]

theorem mulM_add (x y z : P k) :
    mulM b c b' c' t x (y + z) = mulM b c b' c' t x y + mulM b c b' c' t x z := by
  ext <;> simp [mulM] <;> ring

theorem add_mulM (x y z : P k) :
    mulM b c b' c' t (x + y) z = mulM b c b' c' t x z + mulM b c b' c' t y z := by
  ext <;> simp [mulM] <;> ring

theorem mulM_smul (a : k) (x y : P k) :
    mulM b c b' c' t x (a • y) = a • mulM b c b' c' t x y := by
  ext <;> simp [mulM] <;> ring

theorem smul_mulM (a : k) (x y : P k) :
    mulM b c b' c' t (a • x) y = a • mulM b c b' c' t x y := by
  ext <;> simp [mulM] <;> ring

/-- Page 84 (« se vérifient »): `M(b, c; b', c'; t)` is associative, for every
value of the twist `t`, over any commutative ring. -/
theorem mulM_assoc (x y z : P k) :
    mulM b c b' c' t (mulM b c b' c' t x y) z = mulM b c b' c' t x (mulM b c b' c' t y z) := by
  ext <;> simp [mulM] <;> ring

end Line

section Locus

variable {k : Type*} [CommRing k] (b c b' c' t : k)

open P

/-- The quadratic polynomial of the twist line, `Q(t) = t² − bb't + b²c' + b'²c − 4cc'`. -/
def Q : k := t ^ 2 - b * b' * t + (b ^ 2 * c' + b' ^ 2 * c - 4 * c * c')

end Locus

end Grothendieck.Folder83

namespace Grothendieck.Folder83

open TensorProduct

section Azumaya

open scoped Kronecker

variable {k : Type*} [CommRing k]

/-- `M(b, c; b', c'; t)` as a type: `k⁴`, coordinates in the basis `(1, u, v, uv)`. -/
def MAlg (_b _c _b' _c' _t : k) : Type _ := Fin 4 → k

namespace MAlg

variable {b c b' c' t : k}

instance : AddCommGroup (MAlg b c b' c' t) := inferInstanceAs (AddCommGroup (Fin 4 → k))

instance : Module k (MAlg b c b' c' t) := inferInstanceAs (Module k (Fin 4 → k))

/-- The coordinates of an element of `MAlg`, as an element of `P k`. -/
def toP (x : MAlg b c b' c' t) : P k := ⟨x 0, x 1, x 2, x 3⟩

/-- The element of `MAlg` with given coordinates. -/
def ofP (x : P k) : MAlg b c b' c' t := ![x.x0, x.x1, x.x2, x.x3]

omit [CommRing k] in
lemma toP_injective : Function.Injective (toP : MAlg b c b' c' t → P k) := by
  intro x y h
  simp only [toP, P.mk.injEq] at h
  funext i; fin_cases i <;> simp [h]

lemma toP_add (x y : MAlg b c b' c' t) : toP (x + y) = toP x + toP y := rfl

lemma toP_smul (a : k) (x : MAlg b c b' c' t) : toP (a • x) = a • toP x := rfl

lemma toP_zero : toP (0 : MAlg b c b' c' t) = ⟨0, 0, 0, 0⟩ := rfl

instance : Mul (MAlg b c b' c' t) := ⟨fun x y => ofP (mulM b c b' c' t (toP x) (toP y))⟩

instance : One (MAlg b c b' c' t) := ⟨ofP P.one⟩

lemma toP_mul (x y : MAlg b c b' c' t) : toP (x * y) = mulM b c b' c' t (toP x) (toP y) := rfl

lemma toP_one : toP (1 : MAlg b c b' c' t) = P.one := rfl

instance : Ring (MAlg b c b' c' t) :=
  { (inferInstance : AddCommGroup (MAlg b c b' c' t)) with
    mul_assoc := fun x y z => toP_injective (by simp only [toP_mul]; exact mulM_assoc ..)
    one_mul := fun x => toP_injective (by rw [toP_mul, toP_one, one_mulM])
    mul_one := fun x => toP_injective (by rw [toP_mul, toP_one, mulM_one])
    left_distrib := fun x y z => toP_injective (by
      rw [toP_mul, toP_add, toP_add, mulM_add, toP_mul, toP_mul])
    right_distrib := fun x y z => toP_injective (by
      rw [toP_mul, toP_add, toP_add, add_mulM, toP_mul, toP_mul])
    zero_mul := fun x => toP_injective (by rw [toP_mul, toP_zero]; ext <;> simp [mulM])
    mul_zero := fun x => toP_injective (by rw [toP_mul, toP_zero]; ext <;> simp [mulM]) }

instance : Algebra k (MAlg b c b' c' t) :=
  Algebra.ofModule
    (fun a x y => toP_injective (by rw [toP_mul, toP_smul, smul_mulM, toP_smul, toP_mul]))
    (fun a x y => toP_injective (by rw [toP_mul, toP_smul, mulM_smul, toP_smul, toP_mul]))

/-- **Theorem of page 98.** `M(b, c; b', c'; t)` is an Azumaya algebra over `k`
(`IsAzumaya`: finite, projective, faithful, with `M ⊗ Mᵐᵒᵖ → End M` bijective) if and
only if `Q(t) = t² − bb't + b²c' + b'²c − 4cc'` is invertible in `k`. Over any
commutative ring, characteristic `2` included. -/
theorem isAzumaya_iff : IsAzumaya k (MAlg b c b' c' t) ↔ IsUnit (Q b c b' c' t) := by
  sorry

end MAlg

end Azumaya

end Grothendieck.Folder83

end

-- From Challenge/Folder84.lean
@[expose] public section

universe u

namespace Grothendieck.Folder84

open Polynomial TensorProduct

section Coordinates

variable {R : Type*} [CommRing R]

/-- The matrix of `σᵢ : x ↦ ψ(x)Tᵢ − x` in the basis `(eᵢ, xᵢ)` of `Eᵢ`, where
`Tᵢ = 2xᵢ − bᵢeᵢ`: `σᵢ(eᵢ) = −eᵢ`, `σᵢ(xᵢ) = xᵢ − bᵢeᵢ`. -/
def sigmaE (b : R) : Matrix (Fin 2) (Fin 2) R := !![-1, -b; 0, 1]

/-- `σ₁ ⊗ σ₂` on `E₁ ⊗ E₂`, in the basis `(eᵢ ⊗ eⱼ)` indexed by `Fin 2 × Fin 2`
(`0` for `e`, `1` for `x`). -/
def sigmaTensor (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 × Fin 2 → R) :=
  Matrix.mulVecLin (Matrix.kronecker (sigmaE b₁) (sigmaE b₂))

/-- The map `E₁ ⊗ E₂ → E₁ * E₂` of page 63 in coordinates: the coefficient of
`e₁ ⊗ e₂` in the image is `2a + b₂a' + b₁a''` (from `u₁ ⊗ u₂ ↦ 2u₁u₂`,
`u₁ ⊗ x₂ ↦ u₁b₂`, `x₁ ⊗ u₂ ↦ b₁u₂`), that of `x₁ * x₂` is the coefficient of
`x₁ ⊗ x₂`. -/
def starMap (b₁ b₂ : R) : (Fin 2 × Fin 2 → R) →ₗ[R] (Fin 2 → R) where
  toFun v := ![2 * v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0), v (1, 1)]
  map_add' v w := by
    funext i; fin_cases i <;> first | (simp; done) | (simp; ring)
  map_smul' r v := by
    funext i; fin_cases i <;> first | (simp; done) | (simp; ring)

lemma sigmaTensor_apply (b₁ b₂ : R) (v : Fin 2 × Fin 2 → R) :
    sigmaTensor b₁ b₂ v (0, 0) = v (0, 0) + b₂ * v (0, 1) + b₁ * v (1, 0) + b₁ * b₂ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (0, 1) = -v (0, 1) - b₁ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (1, 0) = -v (1, 0) - b₂ * v (1, 1) ∧
    sigmaTensor b₁ b₂ v (1, 1) = v (1, 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | (simp [sigmaTensor, sigmaE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; done)
      | (simp [sigmaTensor, sigmaE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]; ring)

/-- Page 83: `E₁ ⊗ E₂ → E₁ * E₂` kills `Im(σ₁ ⊗ σ₂ − id)`. -/
theorem range_le_ker (b₁ b₂ : R) :
    LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id) ≤ LinearMap.ker (starMap b₁ b₂) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨h0, h1, h2, h3⟩ := sigmaTensor_apply b₁ b₂ v
  simp only [LinearMap.mem_ker, starMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply, h0, h1, h2, h3]
  funext i; fin_cases i <;> first | (simp; done) | (simp; ring)

/-- The induced map `E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂`. -/
noncomputable def coinvMap (b₁ b₂ : R) :
    ((Fin 2 × Fin 2 → R) ⧸ LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id)) →ₗ[R]
      (Fin 2 → R) :=
  (LinearMap.range (sigmaTensor b₁ b₂ - LinearMap.id)).liftQ (starMap b₁ b₂) (range_le_ker b₁ b₂)

/-- **Proposition (page 85), in coordinates.** The map
`E₁ ⊗ E₂ / Im(σ₁ ⊗ σ₂ − id) → E₁ * E₂` is bijective if and only if
`2R + b₁R + b₂R = R`. -/
theorem coinvariants_bijective_iff (b₁ b₂ : R) :
    Function.Bijective (coinvMap b₁ b₂) ↔ Ideal.span {2, b₁, b₂} = ⊤ := by
  sorry

end Coordinates

end Grothendieck.Folder84

open CategoryTheory MonoidalCategory TensorProduct

open CategoryTheory TensorProduct

end

-- From Challenge/Folder85.lean
@[expose] public section

namespace Grothendieck.Folder85

open Matrix

variable {R : Type*} [CommRing R]

/-- The invariant `A` of pages 23 and 27 for `PGL₂`: `(Tr g)² / det g − 2`,
for a lift `g ∈ GL₂(R)`. -/
noncomputable def invA (g : Matrix (Fin 2) (Fin 2) R) : R :=
  g.trace ^ 2 * Ring.inverse g.det - 2

/-- `g` is nowhere scalar: its image in `PGL₂(k(s))` is not `1` for any point
`s` of `Spec R`, that is, `b`, `c`, `a − d` generate the unit ideal. -/
def NullePartScalaire (g : Matrix (Fin 2) (Fin 2) R) : Prop :=
  Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1} = ⊤

/-- **Pages 10, 30, 40.** If `g ∈ GL₂(R)` is nowhere scalar and `g⁵` is scalar
(the image of `g` in `PGL₂` has order 5 on every fibre), then `A(g)` is a root
of `T² + T − 1`. Over any commutative ring. -/
theorem sq_add_sub_of_pow_five (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hns : NullePartScalaire g)
    {c : R} (h5 : g ^ 5 = c • (1 : Matrix (Fin 2) (Fin 2) R)) :
    invA g ^ 2 + invA g - 1 = 0 := by
  sorry

end Grothendieck.Folder85

end

-- From Challenge/Folder86.lean
@[expose] public section

namespace Grothendieck.Folder86

/-- Neighbours of each vertex: `0` and `11` are opposite poles, `1–5` and `6–10` the two
pentagons. -/
def nbrs : Fin 12 → List (Fin 12)
  | 0 => [1, 2, 3, 4, 5]
  | 1 => [0, 2, 5, 6, 7]
  | 2 => [0, 1, 3, 7, 8]
  | 3 => [0, 2, 4, 8, 9]
  | 4 => [0, 3, 5, 9, 10]
  | 5 => [0, 1, 4, 6, 10]
  | 6 => [1, 5, 7, 10, 11]
  | 7 => [1, 2, 6, 8, 11]
  | 8 => [2, 3, 7, 9, 11]
  | 9 => [3, 4, 8, 10, 11]
  | 10 => [4, 5, 6, 9, 11]
  | 11 => [6, 7, 8, 9, 10]

/-- Adjacency in the icosahedron. -/
def Adj (x y : Fin 12) : Prop := y ∈ nbrs x

instance : DecidableRel Adj := fun x y => inferInstanceAs (Decidable (y ∈ nbrs x))

/-- An oriented triangle `(x, y, z)`: a flag (vertex `x`, edge `{x, y}`, face `{x, y, z}`). -/
def Tri (x y z : Fin 12) : Prop := Adj x y ∧ Adj x z ∧ Adj y z

instance (x y z : Fin 12) : Decidable (Tri x y z) := by unfold Tri; infer_instance

/-- The common neighbours of two vertices. -/
def common (x y : Fin 12) : List (Fin 12) :=
  (List.finRange 12).filter (fun z => decide (Adj x z) && decide (Adj y z))

/-- For a face `{x, y, z}`, the third vertex of the other face on the edge `{x, y}`. -/
def other (x y z : Fin 12) : Fin 12 :=
  ((common x y).filter (fun w => w ≠ z)).headD 0

theorem other_spec : ∀ x y z, Tri x y z →
    Adj x (other x y z) ∧ Adj y (other x y z) ∧ other x y z ≠ z := by decide +kernel

theorem other_uniq : ∀ x y z w, Tri x y z → Adj x w → Adj y w → w ≠ z →
    w = other x y z := by decide +kernel

/-- The antipodism: the vertex at distance `3` (`anti_iff`). -/
def anti : Fin 12 → Fin 12 := ![11, 9, 10, 6, 7, 8, 3, 4, 5, 1, 2, 0]

/-- `anti x` is the only vertex that is neither `x`, nor a neighbour of `x`, nor a neighbour
of a neighbour of `x`. -/
theorem anti_iff : ∀ x y, y = anti x ↔ (y ≠ x ∧ ¬ Adj x y ∧ ∀ z, Adj x z → ¬ Adj z y) := by
  decide +kernel

/-- The automorphism group `G` of the icosahedron. -/
abbrev Aut := Adj ≃r Adj

/-- An automorphism is determined on a face by `other`. -/
theorem map_other (g : Aut) {x y z : Fin 12} (h : Tri x y z) :
    g (other x y z) = other (g x) (g y) (g z) := by
  obtain ⟨h1, h2, h3⟩ := other_spec x y z h
  exact other_uniq _ _ _ _ ⟨g.map_rel_iff.2 h.1, g.map_rel_iff.2 h.2.1, g.map_rel_iff.2 h.2.2⟩
    (g.map_rel_iff.2 h1) (g.map_rel_iff.2 h2) (fun e => h3 (g.injective e))

theorem map_anti (g : Aut) (x : Fin 12) : g (anti x) = anti (g x) := by
  obtain ⟨h1, h2, h3⟩ := (anti_iff x (anti x)).1 rfl
  refine (anti_iff (g x) (g (anti x))).2 ⟨fun e => h1 (g.injective e),
    fun e => h2 (g.map_rel_iff.1 e), fun z hz e => ?_⟩
  exact h3 (g.symm z) (by simpa using g.map_rel_iff.1 (by simpa using hz))
    (g.map_rel_iff.1 (by simpa using e))

/-- `ρ₀(s, t)`: with `u, v` the third vertices of the two faces on `{s, t}`, the side
`{Π_{s,u}, Π_{s,v}}` of the link pentagon of `s` opposite `t`. -/
def rho0 (p : Fin 12 × Fin 12) : Fin 12 × Fin 12 :=
  let u := (common p.1 p.2).headD 0
  let v := (common p.1 p.2).getD 1 0
  (other p.1 u p.2, other p.1 v p.2)

/-- Equality of unordered pairs. -/
def UEq (p q : Fin 12 × Fin 12) : Prop := (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)

instance (p q : Fin 12 × Fin 12) : Decidable (UEq p q) := by unfold UEq; infer_instance

/-- The antipodal pair. -/
def antiP (p : Fin 12 × Fin 12) : Fin 12 × Fin 12 := (anti p.1, anti p.2)

/-- Two edges have the same direction: equal, or antipodal, as unordered pairs. -/
def SameDir (p q : Fin 12 × Fin 12) : Prop := UEq p q ∨ UEq p (antiP q)

instance (p q : Fin 12 × Fin 12) : Decidable (SameDir p q) := by unfold SameDir; infer_instance

def IsEdge (p : Fin 12 × Fin 12) : Prop := Adj p.1 p.2

instance (p : Fin 12 × Fin 12) : Decidable (IsEdge p) := by unfold IsEdge; infer_instance

/-- `ρ₀(s, t)` does not depend on which of the two faces is called `u`. -/
theorem rho0_choice : ∀ s t u, Tri s t u →
    UEq (rho0 (s, t)) (other s u t, other s (other s t u) t) := by decide +kernel

theorem rho0_edge : ∀ p, IsEdge p → IsEdge (rho0 p) := by decide +kernel

/-- `ρ₀` passes to directions. -/
theorem rho0_sameDir : ∀ p q, IsEdge p → SameDir p q → SameDir (rho0 p) (rho0 q) := by
  decide +kernel

/-- A labelling of the edges by `Fin 5`. It is not a definition of the trièdres:
`col_eq_iff` shows that two edges have the same label exactly when their directions are
in the same `ρ`-orbit, so the labels name the five orbits. -/
def colTab : Fin 12 → Fin 12 → Fin 5 := ![![0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0],
  ![0, 0, 3, 0, 0, 2, 1, 4, 0, 0, 0, 0],
  ![1, 3, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0],
  ![2, 0, 4, 0, 0, 0, 0, 0, 3, 1, 0, 0],
  ![3, 0, 0, 0, 0, 1, 0, 0, 0, 4, 2, 0],
  ![4, 2, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 4, 2],
  ![0, 4, 2, 0, 0, 0, 0, 0, 1, 0, 0, 3],
  ![0, 0, 0, 3, 0, 0, 0, 1, 0, 2, 0, 4],
  ![0, 0, 0, 1, 4, 0, 0, 0, 2, 0, 3, 0],
  ![0, 0, 0, 0, 2, 0, 4, 0, 0, 3, 0, 1],
  ![0, 0, 0, 0, 0, 0, 2, 3, 4, 0, 1, 0]]

/-- The trièdre of an edge. -/
def col (p : Fin 12 × Fin 12) : Fin 5 := colTab p.1 p.2

/-- `q` lies in the trièdre of `p`: its direction is that of `p`, `ρ p` or `ρ² p`. -/
def SameTri (p q : Fin 12 × Fin 12) : Prop :=
  SameDir q p ∨ SameDir q (rho0 p) ∨ SameDir q (rho0 (rho0 p))

instance (p q : Fin 12 × Fin 12) : Decidable (SameTri p q) := by unfold SameTri; infer_instance

/-- The labels are the `ρ`-orbits of directions: five orbits of three directions. -/
theorem col_eq_iff : ∀ p q, IsEdge p → IsEdge q → (col p = col q ↔ SameTri p q) := by
  decide +kernel

/-- Image of a pair under an automorphism. -/
def gP (g : Aut) (p : Fin 12 × Fin 12) : Fin 12 × Fin 12 := (g p.1, g p.2)

theorem head_tri : ∀ s t, Adj s t → Tri s t ((common s t).headD 0) := by decide +kernel

theorem getD_eq : ∀ s t, Adj s t → (common s t).getD 1 0 = other s t ((common s t).headD 0) := by
  decide +kernel

theorem tri_rot : ∀ x y z, Tri x y z → Tri x z y ∧ Tri x (other x y z) y := by decide +kernel

theorem map_tri (g : Aut) {x y z : Fin 12} (h : Tri x y z) : Tri (g x) (g y) (g z) :=
  ⟨g.map_rel_iff.2 h.1, g.map_rel_iff.2 h.2.1, g.map_rel_iff.2 h.2.2⟩

theorem map_rho0 (g : Aut) (p : Fin 12 × Fin 12) (hp : IsEdge p) :
    UEq (gP g (rho0 p)) (rho0 (gP g p)) := by
  obtain ⟨s, t⟩ := p
  have hu := head_tri s t hp
  set u := (common s t).headD 0
  have e1 : rho0 (s, t) = (other s u t, other s (other s t u) t) := by
    simp only [rho0]; rw [getD_eq s t hp]
  have hg := rho0_choice (g s) (g t) (g u) (map_tri g hu)
  rw [e1]
  have h1 := map_other g (tri_rot _ _ _ hu).1
  have h2 := map_other g (tri_rot _ _ _ hu).2
  have h3 := map_other g hu
  simp only [gP] at hg ⊢
  rw [h1, h2, h3]
  rcases hg with ⟨a, b⟩ | ⟨a, b⟩
  exacts [Or.inl ⟨a.symm, b.symm⟩, Or.inr ⟨b.symm, a.symm⟩]

theorem sameDir_trans' : ∀ a, IsEdge a → ∀ b, SameDir a b → ∀ c, SameDir b c →
    SameDir a c := by decide +kernel

theorem sameDir_trans (a b c : Fin 12 × Fin 12) (ha : IsEdge a) (_ : IsEdge b)
    (h1 : SameDir a b) (h2 : SameDir b c) : SameDir a c := sameDir_trans' a ha b h1 c h2

theorem sameDir_of_ueq : ∀ a b, UEq a b → SameDir a b := fun _ _ h => Or.inl h

theorem map_sameDir (g : Aut) {a b : Fin 12 × Fin 12} (h : SameDir a b) :
    SameDir (gP g a) (gP g b) := by
  simp only [SameDir, UEq, antiP, gP] at h ⊢
  rw [← map_anti, ← map_anti]
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp [h1, h2]

theorem isEdge_map (g : Aut) {p : Fin 12 × Fin 12} (h : IsEdge p) : IsEdge (gP g p) :=
  g.map_rel_iff.2 h

theorem map_sameTri (g : Aut) {p q : Fin 12 × Fin 12} (hp : IsEdge p) (hq : IsEdge q)
    (h : SameTri p q) : SameTri (gP g p) (gP g q) := by
  have hp1 := rho0_edge p hp
  have hp2 := rho0_edge _ hp1
  have gq := isEdge_map g hq
  have m1 := sameDir_of_ueq _ _ (map_rho0 g p hp)
  have m2 := sameDir_of_ueq _ _ (map_rho0 g _ hp1)
  have m3 := rho0_sameDir _ _ (isEdge_map g hp1) m1
  rcases h with h | h | h
  · exact Or.inl (map_sameDir g h)
  · exact Or.inr (Or.inl (sameDir_trans _ _ _ gq (isEdge_map g hp1) (map_sameDir g h) m1))
  · exact Or.inr (Or.inr (sameDir_trans _ _ _ gq (isEdge_map g hp2) (map_sameDir g h)
      (sameDir_trans _ _ _ (isEdge_map g hp2) (rho0_edge _ (isEdge_map g hp1)) m2 m3)))

/-- A vertex adjacent to `0` in each trièdre. -/
def nb0 : Fin 5 → Fin 12 := ![1, 2, 3, 4, 5]

theorem nb0_spec : ∀ c, IsEdge (0, nb0 c) ∧ col (0, nb0 c) = c := by decide

/-- The permutation of the trièdres induced by an automorphism. -/
def actT (g : Aut) (c : Fin 5) : Fin 5 := col (gP g (0, nb0 c))

theorem col_map (g : Aut) {p : Fin 12 × Fin 12} (hp : IsEdge p) :
    col (gP g p) = actT g (col p) := by
  obtain ⟨h0, hc⟩ := nb0_spec (col p)
  have : SameTri p (0, nb0 (col p)) := (col_eq_iff _ _ hp h0).1 hc.symm
  exact ((col_eq_iff _ _ (isEdge_map g hp) (isEdge_map g h0)).2
    (map_sameTri g hp h0 this))

theorem actT_mul (g h : Aut) (c : Fin 5) : actT (g * h) c = actT g (actT h c) := by
  simpa [actT, gP] using col_map g (isEdge_map h (nb0_spec c).1)

theorem actT_one (c : Fin 5) : actT 1 c = c := (nb0_spec c).2

/-- The homomorphism `G → 𝔖_T` (page 22). -/
def permT : Aut →* Equiv.Perm (Fin 5) where
  toFun g :=
    { toFun := actT g
      invFun := actT g⁻¹
      left_inv := fun c => by rw [← actT_mul, inv_mul_cancel, actT_one]
      right_inv := fun c => by rw [← actT_mul, mul_inv_cancel, actT_one] }
  map_one' := Equiv.ext actT_one
  map_mul' g h := Equiv.ext (actT_mul g h)

/-- Page 25: `G → Alt_T` is onto. -/
theorem permT_surjective (σ : Equiv.Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) :
    ∃ g, permT g = σ := by
  sorry

end Grothendieck.Folder86

end

-- From Challenge/Folder88.lean
@[expose] public section

namespace Grothendieck.Folder88

open Equiv

section Ordre

variable {W R I : Type*} [Group W] [MulAction W R]

/-- The data of the reading: a `W`-torsor `R` and `φ : R × I → W` with a)
`φ(w r, i) = w φ(r, i) w⁻¹` and `φ(r, i)² = 1`. -/
structure Epinglage (W R I : Type*) [Group W] [MulAction W R] where
  /-- `φ(r, i)`, the simple reflection of index `i` for the base `r`. -/
  φ : R → I → W
  /-- a) `φ(w r, i) = int(w) φ(r, i)`. -/
  equivariant : ∀ (w : W) r i, φ (w • r) i = w * φ r i * w⁻¹
  /-- `φ(r, i)² = 1`. -/
  involution : ∀ r i, φ r i * φ r i = 1
  /-- `W` acts freely on `R`. -/
  libre : ∀ (w : W) (r : R), w • r = r → w = 1
  /-- `W` acts transitively on `R`. -/
  transitif : ∀ r r' : R, ∃ w : W, w • r = r'

variable (E : Epinglage W R I) (n : ℕ)

/-- `Rep'(I) = Bij([1, ℓ], I)`, with `ℓ = n + 2` and `[1, ℓ]` written
`Fin (n + 2)` (position `k` of the reading is `k - 1` here). -/
abbrev Rep' (n : ℕ) (I : Type*) := Fin (n + 2) ≃ I

/-- The position `ℓ`. -/
def dernier : Fin (n + 2) := Fin.last (n + 1)

/-- The position `ℓ - 1`. -/
def avantDernier : Fin (n + 2) := (Fin.last n).castSucc

/-- `τ_{ℓ-1}`, the transposition of `ℓ - 1` and `ℓ`. -/
def τ : Perm (Fin (n + 2)) := swap (avantDernier n) (dernier n)

/-- `σ_{ℓ-2}(r, u) = (r, u ∘ τ_{ℓ-1})`. -/
def sigmaAvant : Perm (R × Rep' n I) :=
  Function.Involutive.toPerm (fun x => (x.1, (τ n).trans x.2)) fun x => by
    ext k <;> simp [τ, swap_apply_self]

@[simp] theorem sigmaAvant_apply (x : R × Rep' n I) :
    sigmaAvant n x = (x.1, (τ n).trans x.2) := rfl

theorem sigmaDernier_aux (r : R) (i : I) :
    E.φ (E.φ r i • r) i • E.φ r i • r = r := by
  rw [E.equivariant, mul_inv_cancel_right, smul_smul, E.involution, one_smul]

/-- `σ_{ℓ-1}(r, u) = (φ(r, u(ℓ)) · r, u)`. -/
def sigmaDernier : Perm (R × Rep' n I) :=
  Function.Involutive.toPerm (fun x => (E.φ x.1 (x.2 (dernier n)) • x.1, x.2)) fun x => by
    simp only [sigmaDernier_aux]

@[simp] theorem sigmaDernier_apply (x : R × Rep' n I) :
    sigmaDernier E n x = (E.φ x.1 (x.2 (dernier n)) • x.1, x.2) := rfl

variable [Fintype I] [DecidableEq I]

/-- `ν`, the lcm of the `n_{ij}`, `i ≠ j`, computed at a base `r₀`. -/
noncomputable def nu (r₀ : R) : ℕ :=
  ((Finset.univ : Finset (I × I)).filter (fun p => p.1 ≠ p.2)).lcm
    fun p => orderOf (E.φ r₀ p.1 * E.φ r₀ p.2)

/-- **Proposition** (page 8). For `ℓ = n + 2 = Card I` and `R` non-empty, the
order of `σ_{ℓ-2} σ_{ℓ-1}` on `R × Rep'(I)` is `2ν`. -/
theorem proposition_ordre (r₀ : R) (e : Rep' n I) :
    orderOf (sigmaAvant n * sigmaDernier E n) = 2 * nu E r₀ := by
  sorry

end Ordre

end Grothendieck.Folder88

end

-- From Challenge/Folder89.lean
@[expose] public section

namespace Grothendieck.Folder89

variable {R : Type*} [CommRing R]

/-- The wedge `u ∧ v` of two vectors of `R²`: the determinant of the pair. -/
def wedge (u v : Fin 2 → R) : R := u 0 * v 1 - u 1 * v 0

/-- Folder 89, pages 15–18: for `u ∧ v` a unit, `u ∧ v = v ∧ w = w ∧ u` exactly when
`u + v + w = 0`, over any commutative ring. -/
theorem fundamental_relation (u v w : Fin 2 → R) (hd : IsUnit (wedge u v)) :
    (wedge u v = wedge v w ∧ wedge v w = wedge w u) ↔ u + v + w = 0 := by
  sorry

end Grothendieck.Folder89

end

-- From Challenge/Folder90.lean
@[expose] public section

open Polynomial TensorProduct

namespace Grothendieck.Folder90

variable (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]

variable {R K}

variable (R K) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

section Components

variable {A : Type*} [CommRing A] (π : A)

/-- **The criterion for `A` reduced and Noetherian**: `⋂ₙ πⁿA = 0` if and only if every
irreducible component of `Spec A` meets the special fibre `V(π)`. -/
theorem iInf_pow_eq_bot_iff [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ := by
  sorry

end Components

end Grothendieck.Folder90

end

-- From Challenge/Folder90Comodules.lean
@[expose] public section

open TensorProduct LinearMap

namespace Grothendieck.Folder90Comodules

variable {A : Type*} [CommRing A]

/-- A comodule over an `A`-coalgebra `B`: an `A`-module `E` with a coaction `δ : E → B ⊗ E`,
counital and coassociative (page 7 of folder 90; « `A`-`G`-module »). -/
class Comodule (A : Type*) (B E : Type*) [CommRing A] [AddCommGroup B] [Module A B]
    [Coalgebra A B] [AddCommGroup E] [Module A E] where
  coact : E →ₗ[A] B ⊗[A] E
  counit_coact : (TensorProduct.lid A E).toLinearMap ∘ₗ
    (Coalgebra.counit (R := A) (A := B)).rTensor E ∘ₗ coact = LinearMap.id
  coassoc : (TensorProduct.assoc A B B E).toLinearMap ∘ₗ
    (Coalgebra.comul (R := A) (A := B)).rTensor E ∘ₗ coact = coact.lTensor B ∘ₗ coact

variable {B E : Type*} [AddCommGroup B] [Module A B] [Coalgebra A B] [AddCommGroup E] [Module A E]

/-- A submodule `N ⊆ E` is a **subcomodule** (« stable par `G` ») if `δ N ⊆ B ⊗ N`. -/
def IsSubcomodule (B : Type*) [AddCommGroup B] [Module A B] [Coalgebra A B]
    [Comodule A B E] (N : Submodule A E) : Prop :=
  ∀ e ∈ N, Comodule.coact (A := A) (B := B) e ∈ LinearMap.range (N.subtype.lTensor B)

/-- The hypothesis of pages 7 and 13: `B` is the filtered union of submodules `Bᵢ`, finite
projective, with `B ⧸ Bᵢ` flat and `Δ Bᵢ ⊆ Bᵢ ⊗ Bᵢ`. -/
structure Exhaustion (A : Type*) (B : Type*) [CommRing A] [AddCommGroup B] [Module A B]
    [Coalgebra A B] (ι : Type*) where
  Bi : ι → Submodule A B
  nonempty : Nonempty ι
  directed : Directed (· ≤ ·) Bi
  exhaustive : ∀ b : B, ∃ i, b ∈ Bi i
  finite : ∀ i, Module.Finite A (Bi i)
  projective : ∀ i, Module.Projective A (Bi i)
  flat : ∀ i, Module.Flat A (B ⧸ Bi i)
  comul_mem : ∀ i, ∀ b ∈ Bi i, Coalgebra.comul (R := A) b ∈
    LinearMap.range (TensorProduct.map (Bi i).subtype (Bi i).subtype)

namespace Exhaustion

variable {ι : Type*} (H : Exhaustion A B ι)

variable (E) in
/-- The action of `u ∈ Uᵢ` on an element `y ∈ Bᵢ ⊗ E`: `(u ⊗ id) y ∈ E`. When `y` is the
coaction of `e`, this is `u · e` of page 7. -/
noncomputable def coeff (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) : E :=
  TensorProduct.lid A E (u.rTensor E y)

section Comodule

variable [Comodule A B E]

/-- The generators `u · (F ∩ Eᵢ)` of `F′`: the `(u ⊗ id) y` with `y ∈ Bᵢ ⊗ E` lifting `δ f`,
`f ∈ F`, `u ∈ Uᵢ`. -/
def lifts (F : Submodule A E) : Set E :=
  {e | ∃ (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) (f : E), f ∈ F ∧
    (H.Bi i).subtype.rTensor E y = Comodule.coact (A := A) (B := B) f ∧ H.coeff E i y u = e}

/-- **`F′ = Σᵢ Uᵢ · (F ∩ Eᵢ)`** (the formula of the reading, pages 13–15). -/
def closure (F : Submodule A E) : Submodule A E :=
  Submodule.span A (H.lifts F)

/-- **Statement 1) of page 13, for `X = S = Spec A`**: every submodule `F` of a comodule lies
in a smallest subcomodule, `F′`. -/
theorem isLeast_closure (F : Submodule A E) :
    IsLeast {N : Submodule A E | IsSubcomodule B N ∧ F ≤ N} (H.closure F) := by
  sorry

end Comodule

end Exhaustion

end Grothendieck.Folder90Comodules

end

-- From Challenge/Folder93.lean
@[expose] public section

open Polynomial

open scoped Ring

namespace Grothendieck.Folder93

variable {R : Type*} [CommRing R]

local notation "D" => Polynomial.hasseDeriv

/-- Numerator of `G₀`: `G₀(t, f) · (D⁽¹⁾f)² = (D⁽²⁾f)² − D⁽³⁾f · D⁽¹⁾f`. -/
noncomputable def N (f : R[X]) : R[X] := D 2 f ^ 2 - D 3 f * D 1 f

open CategoryTheory CochainComplex HomComplex

end Grothendieck.Folder93

namespace Grothendieck.Folder93.Alpha

open Polynomial

open scoped Ring

local notation "D" => Polynomial.hasseDeriv

variable {A : Type*} [CommRing A] (p n : ℕ) (α : A)

/-- `T^(p^n) − α`. -/
noncomputable abbrev P : A[X] := X ^ p ^ n - C α

variable {p n α}

variable (p n α)

/-- The Proposition of pages 121–123 in `B = A[T]/(T^(p^n) − α)` for a local ring `A`
(so `Pic(A) = 0`), `α` arbitrary: if `C(k,3)` is a unit for `3 ≤ k < p^n`, `D⁽¹⁾s` is a unit
of `B` and `G₀(t, s) = 0` in `B`, then `s = (at + b)/(ct + d)` in `B` with `a, b, c, d ∈ A`
and `ct + d` a unit of `B`. -/
theorem rigidity_alpha_local [IsLocalRing A] [Fact p.Prime] [CharP A p] (hq : 3 < p ^ n)
    (hC : ∀ k, 3 ≤ k → k < p ^ n → IsUnit ((k.choose 3 : ℕ) : A)) (s : A[X])
    (hs : IsUnit (AdjoinRoot.mk (P p n α) (D 1 s))) (hN : AdjoinRoot.mk (P p n α) (N s) = 0) :
    ∃ a b c d : A,
      AdjoinRoot.mk (P p n α) (s * (C c * X + C d)) = AdjoinRoot.mk (P p n α) (C a * X + C b) ∧
      IsUnit (AdjoinRoot.mk (P p n α) (C c * X + C d)) := by
  sorry

end Grothendieck.Folder93.Alpha

end

-- From Challenge/Folder94.lean
@[expose] public section

open RingTheory.Sequence Submodule Function

namespace Grothendieck.Folder94

variable {A : Type*} [CommRing A]

open Polynomial

noncomputable section

universe u

section Telescope

variable {R : Type*} [CommRing R] (c : ℕ → R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The transition maps of the telescope `M →c M →c M → ⋯` from stage `i` to stage `j`:
multiplication by `∏_{i < l ≤ j} c l`. -/
def teleMap (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M := (∏ l ∈ Finset.Ioc i j, c l) • LinearMap.id

/-- The functor `F(M) = colim(M →c M →c M → ⋯)` of the counterexample. -/
abbrev Tele : Type _ := Module.DirectLimit (fun _ : ℕ => M) (teleMap c M)

variable {c M}

end Telescope

section Plane

variable {k : Type*} [Field k]

/-- `x − a` in `k[x, y]`, written `k[X][X]` with `x` the inner variable. -/
abbrev hx (a : k) : k[X][X] := C (X - C a)

/-- Hence `F` restricted to `A_g`-modules is representable by no finite module, for any
`g ≠ 0`: the case `𝔭 = 0` of Lemma 5 (v) fails. -/
theorem not_representable_away {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0)
    (Q : Type*) [AddCommGroup Q] [Module (Localization.Away g) Q]
    [Module.Finite (Localization.Away g) Q]
    (e : (Q →ₗ[Localization.Away g] Localization.Away g) ≃ₗ[Localization.Away g]
      Tele (fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j))) (Localization.Away g)) :
    False := by
  sorry

end Plane

end

end Grothendieck.Folder94

end

-- From Challenge/Folder98.lean
@[expose] public section

namespace Grothendieck.Folder98

variable {X Y Z : Type*}

section ExampleIII

open Topology

variable {Γ : Type*} [Group Γ] {X : Type*} [MulAction Γ X]
  {E F : Type*} [MulAction Γ E] [MulAction Γ F]

variable (Γ X) in
/-- `Φ(E) = X ×^Γ E`, the contracted product. -/
abbrev Phi (E : Type*) [MulAction Γ E] := Quotient (MulAction.orbitRel Γ (X × E))

variable (Γ X) in
/-- `Φ(f) : X ×^Γ E → X ×^Γ F` for an equivariant `f : E → F`. -/
def Phi.map (f : E → F) (hf : ∀ (g : Γ) e, f (g • e) = g • f e) : Phi Γ X E → Phi Γ X F :=
  Quotient.map (Prod.map id f) fun _ b ⟨g, h⟩ => ⟨g, h ▸ Prod.ext rfl (hf g b.2).symm⟩

section Topology

variable [TopologicalSpace X] [ContinuousConstSMul Γ X] [TopologicalSpace E] [DiscreteTopology E]
  [TopologicalSpace F] [DiscreteTopology F]

/-- Example III: for `Γ` acting on `X` with every point having a neighbourhood disjoint from its
translates, `Φ` takes every equivariant map of discrete `Γ`-sets to a covering map; by
`hasDeg_phi`, one with `r` sheets when the map has degree `r`. -/
theorem isCoveringMap_phi
    (hdisj : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : Γ, ((g • ·) '' U ∩ U).Nonempty → g = 1)
    {f : E → F} (hf : ∀ (g : Γ) e, f (g • e) = g • f e) : IsCoveringMap (Phi.map Γ X f hf) := by
  sorry

end Topology

end ExampleIII

end Grothendieck.Folder98

end

-- From Challenge/Folder100.lean
@[expose] public section

namespace Grothendieck.Folder100.Baire

open IsLocalRing PrimeSpectrum

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

variable [IsAdicComplete (maximalIdeal R) R]

/-- The Proposition of page 36 for any countable index set. -/
theorem exists_finite_subcover_of_countable {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hcov : ∀ x : PrimeSpectrum R, Order.coheight x ≤ 1 → x ∈ ⋃ i, Z i) :
    ∃ s : Finset ι, ⋃ i ∈ s, Z i = Set.univ := by
  sorry

end Grothendieck.Folder100.Baire

end

-- From Challenge/Folder101.lean
@[expose] public section

namespace Grothendieck.Folder101

open IsLocalRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- `A` inside its fraction field `K`. -/
abbrev Aₖ : Submodule A K := LinearMap.range (Algebra.linearMap A K)

/-- `K/A = H¹_x(O_X)`, the module `I` of the page. -/
abbrev KA := K ⧸ Aₖ A K

variable {A K}

variable {M₀ M₁ : Type*} [AddCommGroup M₀] [Module A M₀] [AddCommGroup M₁] [Module K M₁]
  [Module A M₁] [IsScalarTower A K M₁] (u : M₀ →ₗ[A] M₁)

variable (K) in
/-- `Ext⁰(X; F, O_X)` for `F = (M₀, M₁, u)`: the kernel of
`Hom_K(M₁, K) → Hom_A(M₀, K/A)`, `g ↦ g ∘ u mod A`. -/
def Ext0 := {g : M₁ →ₗ[K] K // ∀ m, g (u m) ∈ Aₖ A K}

/-- The duality map on `Ext⁰`, to `Hom_A(Coker u, K/A) = Hom_A(H¹_x(F), I)`. -/
def phi0 (g : Ext0 K u) : (M₁ ⧸ LinearMap.range u) →ₗ[A] KA A K :=
  (LinearMap.range u).liftQ ((Aₖ A K).mkQ ∘ₗ g.1.restrictScalars A) (by
    rintro _ ⟨m, rfl⟩
    simpa [LinearMap.mem_ker] using g.2 m)

variable (K) in
/-- The image of `Hom_K(M₁, K) → Hom_A(M₀, K/A)`. -/
def imD : Submodule A (M₀ →ₗ[A] KA A K) where
  carrier := {h | ∃ g : M₁ →ₗ[K] K, ∀ m, h m = Submodule.Quotient.mk (g (u m))}
  add_mem' := fun ⟨g, hg⟩ ⟨g', hg'⟩ => ⟨g + g', fun m => by simp [hg, hg']⟩
  zero_mem' := ⟨0, fun m => by simp⟩
  smul_mem' a _ := fun ⟨g, hg⟩ => ⟨algebraMap A K a • g, fun m => by
    simp [hg, Algebra.smul_def, ← Submodule.Quotient.mk_smul]⟩

variable (K) in
/-- `Ext¹(X; F, O_X)`: the cokernel of `Hom_K(M₁, K) → Hom_A(M₀, K/A)`. -/
abbrev Ext1 := (M₀ →ₗ[A] KA A K) ⧸ imD K u

/-- The duality map on `Ext¹`, to `Hom_A(Ker u, K/A) = Hom_A(H⁰_x(F), I)`: restriction. -/
def phi1 : Ext1 K u →ₗ[A] (LinearMap.ker u →ₗ[A] KA A K) :=
  (imD K u).liftQ (LinearMap.lcomp A _ (LinearMap.ker u).subtype) (by
    rintro h ⟨g, hg⟩
    rw [LinearMap.mem_ker]
    ext ⟨m, hm⟩
    simp [hg, LinearMap.mem_ker.1 hm])

/-- **Local duality in dimension one, for every `O_X`-module** (pages 10–11), in the page's
model: for `A` a complete discrete valuation ring and any triple `(M₀, M₁, u)`, the duality
maps `Ext⁰ → Hom_A(Coker u, K/A)` and `Ext¹ → Hom_A(Ker u, K/A)` are bijective. -/
theorem duality_dim_one [IsAdicComplete (maximalIdeal A) A] :
    Function.Bijective (phi0 (K := K) u) ∧ Function.Bijective (phi1 (K := K) u) := by
  sorry

end Grothendieck.Folder101

end

-- From Challenge/Folder104.lean
@[expose] public section

namespace Grothendieck.Folder104

open CategoryTheory

section Epinglage

open Opposite Limits

universe w

variable {M : Type w} [SmallCategory M]

/-- `I_D`: the sub-objects of `D` in a skeletal `M` satisfying (i) and (ii), that is, by (*),
the arrows `D' → D`. -/
abbrev Sous (D : M) : Type w := Σ D' : M, (D' ⟶ D)

/-- The order of `I_D`: `(D', a) ≤ (D'', b)` iff `a` factors through `b`. -/
def Sous.le {D : M} (y y' : Sous D) : Prop := ∃ w : y.1 ⟶ y'.1, w ≫ y'.2 = y.2

variable (M) in
/-- **An `M`-pinned poset** (pages 12–13): a poset `K`, a strictly increasing type map
`τ_K : K → N` (here `N` is the skeletal `M` itself, ordered by the existence of an arrow), and
for each `ξ` of type `n` an isomorphism `u_ξ : I_n ≅ K_{≤ξ}` with `u_ξ(d_n) = ξ`, satisfying
(1) `τ_K ∘ u_ξ = τ_n` and (2) `u_ξ ∘ u^n_y = u_{u_ξ(y)}`. -/
structure Epingle where
  /-- The poset. -/
  K : Type w
  [ordre : PartialOrder K]
  /-- The type map `τ_K`. -/
  τ : K → M
  τ_strict : ∀ ξ η : K, ξ < η → Nonempty (τ ξ ⟶ τ η) ∧ τ ξ ≠ τ η
  /-- The pinning `u_ξ : I_{τ ξ} → K`. -/
  u : (ξ : K) → Sous (τ ξ) → K
  u_top : ∀ ξ, u ξ ⟨τ ξ, 𝟙 _⟩ = ξ
  u_injective : ∀ ξ, Function.Injective (u ξ)
  u_range : ∀ ξ, Set.range (u ξ) = Set.Iic ξ
  u_le : ∀ ξ y y', u ξ y ≤ u ξ y' ↔ Sous.le y y'
  /-- (1) -/
  τ_u : ∀ ξ y, τ (u ξ y) = y.1
  /-- (2) -/
  u_u : ∀ ξ (y : Sous (τ ξ)) (z : Sous y.1),
    u (u ξ y) ⟨z.1, z.2 ≫ eqToHom (τ_u ξ y).symm⟩ = u ξ ⟨z.1, z.2 ≫ y.2⟩

attribute [instance] Epingle.ordre

/-- The morphisms of `M`-pinned posets (page 13): strictly increasing maps `f` with
`τ_L ∘ f = τ_K` making the triangles `u^L_{f ξ} = f ∘ u^K_ξ` commute. -/
@[ext]
structure Epingle.Hom (K L : Epingle M) where
  /-- The underlying map. -/
  f : K.K → L.K
  strictMono : StrictMono f
  τ_f : ∀ ξ, L.τ (f ξ) = K.τ ξ
  u_f : ∀ ξ y, f (K.u ξ y) = L.u (f ξ) ⟨y.1, y.2 ≫ eqToHom (τ_f ξ).symm⟩

instance : Category (Epingle M) where
  Hom := Epingle.Hom
  id K := ⟨id, strictMono_id, fun _ => rfl, fun _ _ => by simp⟩
  comp φ ψ := ⟨ψ.f ∘ φ.f, ψ.strictMono.comp φ.strictMono,
    fun ξ => (ψ.τ_f _).trans (φ.τ_f ξ), fun ξ y => by simp [φ.u_f, ψ.u_f]⟩

@[ext]
lemma Epingle.hom_ext {K L : Epingle M} {φ ψ : K ⟶ L} (h : φ.f = ψ.f) : φ = ψ :=
  Epingle.Hom.ext h

end Epinglage

section Prefaisceaux

open Opposite Limits

universe w

variable {M : Type w} [SmallCategory M]

/-- A presheaf is **non-singular** when each of its elements `x ∈ X(D)` is a monomorphism
`yoneda D → X`, that is, `a ↦ X(a)(x)` is injective. -/
def NonSingulier (X : Mᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃D D' : M⦄ (x : X.obj (op D)) (a b : D' ⟶ D), X.map a.op x = X.map b.op x → a = b

/-- A sub-object of `X` is a *model* if it is isomorphic to an object of `M`. -/
def EstModele {X : Mᵒᵖ ⥤ Type w} (S : Subfunctor X) : Prop :=
  ∃ D : M, Nonempty (S.toFunctor ≅ yoneda.obj D)

/-- **The admissible objects** of page 12: `X` is the supremum of its model sub-objects, and the
intersection of two model sub-objects is the supremum of the model sub-objects it contains. -/
def Admissible (X : Mᵒᵖ ⥤ Type w) : Prop :=
  sSup {S : Subfunctor X | EstModele S} = ⊤ ∧
    ∀ S T : Subfunctor X, EstModele S → EstModele T →
      S ⊓ T = sSup {R | EstModele R ∧ R ≤ S ⊓ T}

lemma nonSingulier_iff_mono (X : Mᵒᵖ ⥤ Type w) :
    NonSingulier X ↔ ∀ (D : M) (x : X.obj (op D)), Mono (yonedaEquiv.symm x) := by
  simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
  refine ⟨fun h D x U a b hab => h x a b hab, fun h D D' x a b hab => h D x (op D') hab⟩

/-- The model sub-object generated by an element of a non-singular presheaf. -/
noncomputable def modeleEngendre {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) :
    Subfunctor X :=
  Subfunctor.range (yonedaEquiv.symm x)

lemma mem_modeleEngendre {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) :
    x ∈ (modeleEngendre x).obj (op D) :=
  ⟨𝟙 D, by simp [yonedaEquiv_symm_app_apply]⟩

lemma modeleEngendre_le {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) (T : Subfunctor X)
    (hx : x ∈ T.obj (op D)) : modeleEngendre x ≤ T := by
  rintro U _ ⟨a, rfl⟩
  exact T.map a.op hx

lemma estModele_modeleEngendre {X : Mᵒᵖ ⥤ Type w} (hX : NonSingulier X) {D : M}
    (x : X.obj (op D)) : EstModele (modeleEngendre x) := by
  have := (nonSingulier_iff_mono X).1 hX D x
  exact ⟨D, ⟨(asIso (Subfunctor.toRange (yonedaEquiv.symm x))).symm⟩⟩

variable (hmono : ∀ {X Y : M} (f : X ⟶ Y), Mono f)

include hmono in
/-- **Page 12, read in the presheaf language.** When every arrow of `M` is a monomorphism, a
presheaf is admissible iff it is non-singular: every element is a monomorphism `yoneda D → X`.
The first condition of page 12 alone implies it; the second then follows. -/
theorem admissible_iff (X : Mᵒᵖ ⥤ Type w) : Admissible X ↔ NonSingulier X := by
  constructor
  · rintro ⟨h1, -⟩ D D' x a b hab
    have hx : x ∈ (sSup {S : Subfunctor X | EstModele S}).obj (op D) := by rw [h1]; trivial
    simp only [Subfunctor.sSup_obj, Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_image,
      Set.mem_ofPred_eq] at hx
    obtain ⟨_, ⟨S, ⟨E, ⟨e⟩⟩, rfl⟩, hxS⟩ := hx
    let s : S.toFunctor.obj (op D) := ⟨x, hxS⟩
    have hs : S.toFunctor.map a.op s = S.toFunctor.map b.op s := Subtype.ext hab
    have na := NatTrans.naturality_apply e.hom a.op s
    have nb := NatTrans.naturality_apply e.hom b.op s
    rw [hs, nb] at na
    simp only [yoneda_obj_map, Quiver.Hom.unop_op] at na
    exact (cancel_mono (e.hom.app (op D) s)).1 na.symm
  · intro hX
    refine ⟨eq_top_iff.2 fun U x _ => ?_, fun S T _ _ => le_antisymm (fun U z hz => ?_)
      (sSup_le fun R hR => hR.2)⟩
    · exact (le_sSup (estModele_modeleEngendre hX x) : modeleEngendre x ≤ _) U
        (mem_modeleEngendre x)
    · exact (le_sSup (show modeleEngendre z ∈ {R | EstModele R ∧ R ≤ S ⊓ T} from
        ⟨estModele_modeleEngendre hX z, modeleEngendre_le z _ hz⟩)) U (mem_modeleEngendre z)

variable (hend : ∀ {X : M} (f : X ⟶ X), f = 𝟙 X) (hsk : Skeletal M)

/-- The elements of `X`, pairs `(D, x)` with `x ∈ X(D)`: in a skeletal `M`, the model
sub-objects of a non-singular `X`. -/
abbrev Elem (X : Mᵒᵖ ⥤ Type w) : Type w := Σ D : M, X.obj (op D)

include hend hsk in
lemma eq_of_aller_retour {D E : M} (a : D ⟶ E) (b : E ⟶ D) : D = E :=
  hsk ⟨⟨a, b, hend _, hend _⟩⟩

include hend hsk in
/-- The order of `X̃`: `(D', x') ≤ (D, x)` iff `x' = X(a)(x)` for an arrow `a : D' → D`. -/
@[instance_reducible]
def ordreElem (X : Mᵒᵖ ⥤ Type w) : PartialOrder (Elem X) where
  le p q := ∃ a : p.1 ⟶ q.1, X.map a.op q.2 = p.2
  le_refl p := ⟨𝟙 _, by simp⟩
  le_trans p q r := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a ≫ b, by simp [hb, ha]⟩
  le_antisymm := by
    rintro ⟨D, x⟩ ⟨E, y⟩ ⟨a, ha⟩ ⟨b, hb⟩
    dsimp at a b ha hb
    obtain rfl := eq_of_aller_retour hend hsk a b
    rw [hend a] at ha
    simp only [op_id, Functor.map_id_apply] at ha
    rw [ha]

/-- **The `M`-pinned poset `X̃` of a non-singular presheaf** (page 12): its elements with the
type map `(D, x) ↦ D` and the pinning `u_{(D,x)}(D', a) = (D', X(a)(x))`. -/
def versEpingleObj (X : Mᵒᵖ ⥤ Type w) (hX : NonSingulier X) : Epingle M :=
  letI := ordreElem hend hsk X
  { K := Elem X
    τ := Sigma.fst
    τ_strict := by
      rintro ⟨D, x⟩ ⟨E, y⟩ hlt
      obtain ⟨⟨a, ha⟩, hn⟩ := lt_iff_le_not_ge.1 hlt
      refine ⟨⟨a⟩, fun h => hn ?_⟩
      dsimp at h a ha
      subst h
      rw [hend a] at ha
      exact ⟨𝟙 _, by simpa using ha.symm⟩
    u := fun ξ y => ⟨y.1, X.map y.2.op ξ.2⟩
    u_top := fun ξ => by simp
    u_injective := by
      rintro ξ ⟨E, c⟩ ⟨E', c'⟩ h
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
      rw [hX ξ.2 c c' (eq_of_heq h)]
    u_range := by
      intro ξ
      ext q
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.2, rfl⟩
      · rintro ⟨a, ha⟩
        exact ⟨⟨q.1, a⟩, by dsimp only; rw [ha]⟩
    u_le := by
      rintro ξ ⟨E, c⟩ ⟨E', c'⟩
      change (∃ w : E ⟶ E', _) ↔ ∃ w : E ⟶ E', w ≫ c' = c
      refine exists_congr fun w => ⟨fun h => hX ξ.2 _ _ ?_, fun h => ?_⟩
      · simpa using h
      · simp [← h]
    τ_u := fun _ _ => rfl
    u_u := fun ξ y z => by simp }

/-- A natural transformation gives a morphism of pinned posets, `(D, x) ↦ (D, α(x))`. -/
def versEpingleMap {X Y : Mᵒᵖ ⥤ Type w} (hX : NonSingulier X) (hY : NonSingulier Y)
    (α : X ⟶ Y) : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY where
  f p := ⟨p.1, α.app _ p.2⟩
  strictMono := by
    rintro ⟨D, x⟩ ⟨E, y⟩ hlt
    obtain ⟨⟨a, ha⟩, hn⟩ := lt_iff_le_not_ge.1 hlt
    refine lt_iff_le_not_ge.2
      ⟨⟨a, by rw [← NatTrans.naturality_apply]; exact congrArg _ ha⟩, fun ⟨b, hb⟩ => hn ?_⟩
    dsimp at a b ha hb
    obtain rfl := eq_of_aller_retour hend hsk a b
    rw [hend a] at ha
    exact ⟨𝟙 _, by simpa using ha.symm⟩
  τ_f _ := rfl
  u_f := by
    rintro ⟨D, x⟩ ⟨E, (c : E ⟶ D)⟩
    change (⟨E, α.app _ (X.map c.op x)⟩ : Elem Y) = ⟨E, Y.map (c ≫ 𝟙 D).op (α.app _ x)⟩
    rw [Category.comp_id, NatTrans.naturality_apply]

/-- The category `𝔹₀` of admissible presheaves, a full subcategory of `M̂`. -/
abbrev Adm (M : Type w) [SmallCategory M] :=
  ObjectProperty.FullSubcategory (Admissible (M := M))

include hmono in
/-- **The functor `X ↦ X̃`** from admissible presheaves to `M`-pinned posets. -/
def versEpingle : Adm M ⥤ Epingle M where
  obj X := versEpingleObj hend hsk X.obj ((admissible_iff hmono _).1 X.property)
  map α := versEpingleMap hend hsk _ _ α.hom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

include hmono in
/-- **Page 13, « est équivalente à ».** For a skeletal `M` satisfying (i) and (ii), `X ↦ X̃` is
an equivalence between the admissible presheaves on `M` and the `M`-pinned posets. -/
theorem versEpingle_isEquivalence : (versEpingle hmono hend hsk).IsEquivalence := by
  sorry

end Prefaisceaux

end Grothendieck.Folder104

end

-- From Challenge/Folder106.lean
@[expose] public section

namespace Grothendieck.Folder106

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- A *catégorie à cofibrations* in the sense of Baues, as the reading's
conventions footnote recalls axioms C1–C3, on a category with an initial
object `∅`. -/
class CategorieACofibrations (W cof : MorphismProperty C) : Prop where
  /-- C1: isomorphisms are weak equivalences. -/
  iso_W : ∀ {x y : C} (e : x ≅ y), W e.hom
  /-- C1: isomorphisms are cofibrations. -/
  iso_cof : ∀ {x y : C} (e : x ≅ y), cof e.hom
  /-- C1: composites of cofibrations are cofibrations. -/
  cof_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), cof f → cof g → cof (f ≫ g)
  /-- C1, two-out-of-three: the composite of two weak equivalences is one. -/
  W_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W f → W g → W (f ≫ g)
  /-- C1, two-out-of-three: if `f` and `f ≫ g` are weak equivalences, so is `g`. -/
  W_of_comp_left : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W f → W (f ≫ g) → W g
  /-- C1, two-out-of-three: if `g` and `f ≫ g` are weak equivalences, so is `f`. -/
  W_of_comp_right : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), W g → W (f ≫ g) → W f
  /-- C2: the pushout along a cofibration exists. -/
  hasPushout : ∀ {b a y : C} (c : b ⟶ a) (u : b ⟶ y), cof c → HasPushout c u
  /-- C2: in a pushout square `c ≫ u' = u ≫ c'` with `c : b → a` a cofibration,
  `c' : y → a ∨_b y` is a cofibration. -/
  pushout_cof : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → cof c'
  /-- C2: … and a weak equivalence if `c` is one. -/
  pushout_W_of_W : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → W c → W c'
  /-- C2: `u' : a → a ∨_b y` is a weak equivalence if `u` is one. -/
  pushout_W_of_W' : ∀ {b a y p : C} {c : b ⟶ a} {u : b ⟶ y} {u' : a ⟶ p} {c' : y ⟶ p},
    IsPushout c u u' c' → cof c → W u → W u'
  /-- C3: every arrow factors as a cofibration followed by a weak equivalence. -/
  factorisation : ∀ {x y : C} (f : x ⟶ y),
    ∃ (z : C) (i : x ⟶ z) (p : z ⟶ y), cof i ∧ W p ∧ i ≫ p = f

/-- An object `x` is *cofibrant* when `∅ → x` is a cofibration. -/
def Cofibrant (cof : MorphismProperty C) (x : C) : Prop := cof (initial.to x)

variable {W cof : MorphismProperty C} [CategorieACofibrations W cof]

namespace CategorieACofibrations

omit [HasInitial C] in
include cof in
lemma W_id (x : C) : W (𝟙 x) := iso_W (cof := cof) (Iso.refl x)

omit [HasInitial C] in
open Localization.Construction in
@[reassoc (attr := simp)]
lemma wInv_hom {x y : C} (w : x ⟶ y) (hw : W w) : wInv w hw ≫ W.Q.map w = 𝟙 _ :=
  (wIso w hw).inv_hom_id

variable (W cof) in
/-- **Page 11, an object of `Ch'₀(x, y)`**: a diagram `x → ỹ ← y`, the first
arrow a cofibration, the second a weak equivalence. -/
structure Span (x y : C) where
  /-- the middle object `ỹ` -/
  pt : C
  /-- the forward arrow `x → ỹ` -/
  f : x ⟶ pt
  /-- the backward arrow `y → ỹ` -/
  i : y ⟶ pt
  hf : cof f
  hi : W i

namespace Span

variable {x y z w : C}

/-- An arrow `(f, i) → (f', i')` of `Ch'₀(x, y)`: `u : ỹ → ỹ'` with `u f = f'`
and `u i = i'`. Two diagrams lie in the same connected component of `Ch'₀(x, y)`
when they are related by the equivalence relation this generates. -/
def Arrow (s t : Span W cof x y) : Prop := ∃ u : s.pt ⟶ t.pt, s.f ≫ u = t.f ∧ s.i ≫ u = t.i

/-- The fraction `[i]⁻¹[f] : x → y` in `W⁻¹𝒞` of a diagram `(f, i)`. -/
noncomputable def frac (s : Span W cof x y) : W.Q.obj x ⟶ W.Q.obj y :=
  W.Q.map s.f ≫ Localization.Construction.wInv s.i s.hi

omit [HasInitial C] [CategorieACofibrations W cof] in
lemma frac_eq_of_arrow {s t : Span W cof x y} (h : Arrow s t) : s.frac = t.frac := by
  obtain ⟨u, h1, h2⟩ := h
  unfold frac
  have := W.Q_inverts t.i t.hi
  rw [← cancel_mono (W.Q.map t.i)]
  simp only [Category.assoc, wInv_hom, Category.comp_id]
  rw [← h2, W.Q.map_comp, wInv_hom_assoc, ← W.Q.map_comp, h1]

end Span

open Span

variable (W cof) in
/-- `π₀ Ch'₀(x, y)`, the set of connected components of `Ch'₀(x, y)`. -/
abbrev Pi0 (x y : C) : Type _ := Quot (Span.Arrow (W := W) (cof := cof) (x := x) (y := y))

/-- The map `π₀ Ch'₀(x, y) → W⁻¹𝒞(x, y)`, `(f, i) ↦ [i]⁻¹[f]`: the functor
`q'` of page 15 on arrows. -/
noncomputable def qbar {x y : C} : Pi0 W cof x y → (W.Q.obj x ⟶ W.Q.obj y) :=
  Quot.lift Span.frac (fun _ _ h => frac_eq_of_arrow h)

/-- The diagram `(1_x, i) : x → x ← y` of a section `i` of `f : x → y` in `W`. -/
@[reducible] def sectionSpan {x y : C} (f : x ⟶ y) (hf : W f) (i : y ⟶ x) (hi : i ≫ f = 𝟙 y) :
    Span W cof x y :=
  ⟨x, 𝟙 x, i, iso_cof (W := W) (cof := cof) (Iso.refl x),
    W_of_comp_right (cof := cof) i f hf (hi ▸ W_id (cof := cof) y)⟩

variable (W cof) in
/-- **The criterion `(⋆⋆)` of page 15.** For `f : x → y` in `W` and two sections
`i, i'` of `f`, the diagrams `(1_x, i)` and `(1_x, i')` lie in the same connected
component of `Ch'₀(x, y)`. -/
def Critere : Prop :=
  ∀ ⦃x y : C⦄ (f : x ⟶ y) (hf : W f) (i i' : y ⟶ x) (hi : i ≫ f = 𝟙 y) (hi' : i' ≫ f = 𝟙 y),
    Relation.EqvGen Span.Arrow (sectionSpan (cof := cof) f hf i hi) (sectionSpan f hf i' hi')

/-- **The final statement of page 15, as the finding states it**: when every
object is cofibrant, `q'` is faithful if and only if `(⋆⋆)` holds. (Both sides
hold: `fidele`, `critere`.) -/
theorem fidele_iff_critere (hcof : ∀ x : C, Cofibrant cof x) :
    (∀ x y : C, Function.Injective (qbar (W := W) (cof := cof) (x := x) (y := y))) ↔
      Critere W cof := by
  sorry

end CategorieACofibrations

end Grothendieck.Folder106

end

-- From Challenge/Folder107.lean
@[expose] public section

namespace Grothendieck.Folder107

open CategoryTheory Limits HomotopicalAlgebra

universe v u

variable {C : Type u} [Category.{v} C]

/-- A relative cylinder on `i : X ⟶ X'`: precylinders `X ⊗ J`, `X' ⊗ J` and a
map `i ⊗ J : X ⊗ J ⟶ X' ⊗ J` compatible with both ends (folder 107, p. 22). -/
structure RelativeCylinder {X X' : C} (i : X ⟶ X') where
  /-- The cylinder `X ⊗ J`. -/
  P : Precylinder X
  /-- The cylinder `X' ⊗ J`. -/
  P' : Precylinder X'
  /-- The map `i ⊗ J`. -/
  iJ : P.I ⟶ P'.I
  w₀ : P.i₀ ≫ iJ = i ≫ P'.i₀
  w₁ : P.i₁ ≫ iJ = i ≫ P'.i₁

attribute [reassoc] RelativeCylinder.w₀ RelativeCylinder.w₁

/-- `H` is a homotopy from `f` to `f'` on the precylinder `P`. -/
def IsHomotopy {A Y : C} (P : Precylinder A) (H : P.I ⟶ Y) (f f' : A ⟶ Y) : Prop :=
  P.i₀ ≫ H = f ∧ P.i₁ ≫ H = f'

section ModelCategory

variable [ModelCategory C] {X X' Y Y' : C} {i : X ⟶ X'} (R : RelativeCylinder i)

/-- **Pages 20 and 22 in a model category.** With `p` a fibration and the
corner map of the relative cylinder a trivial cofibration, the diagonal `φ`
can be rectified if and only if the homotopies can be chosen compatible. -/
theorem rectification_modelCategory (p : Y ⟶ Y') [Fibration p]
    [Cofibration (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    [WeakEquivalence (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (φ : X' ⟶ Y) :
    (∃ (φbar : X' ⟶ Y) (K : R.P'.I ⟶ Y),
        i ≫ φbar = g ∧ φbar ≫ p = g' ∧ IsHomotopy R.P' K φ φbar) ↔
      ∃ (k : R.P.I ⟶ Y) (h : R.P'.I ⟶ Y'),
        IsHomotopy R.P k (i ≫ φ) g ∧ IsHomotopy R.P' h (φ ≫ p) g' ∧ k ≫ p = R.iJ ≫ h := by
  sorry

end ModelCategory

end Grothendieck.Folder107

end

-- From Challenge/Folder113.lean
@[expose] public section

namespace Grothendieck.Folder113

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Idempotents.Karoubi CategoryTheory.Limits Opposite

universe v u v' u'

variable (P : Type u) [Category.{v} P]

variable (D : Type u') [Category.{v'} D]

variable [Preadditive P] [Preadditive D]

/-- The restriction functor on additive functors. -/
def restrictionAdditive : ((Karoubi P)ᵒᵖ ⥤+ D) ⥤ (Pᵒᵖ ⥤+ D) :=
  (additiveFunctor Pᵒᵖ D).lift
    (AdditiveFunctor.forget _ _ ⋙ (Functor.whiskeringLeft Pᵒᵖ (Karoubi P)ᵒᵖ D).obj (toKaroubi P).op)
    (fun F => by
      change ((toKaroubi P).op ⋙ F.obj).Additive
      infer_instance)

/-- The case of modules: `(Kar P)^k ≃ P^k` with values in `k`-modules. -/
theorem morita_module (k : Type u') [CommRing k] :
    (restrictionAdditive P (ModuleCat.{u'} k)).IsEquivalence := by
  sorry

end Grothendieck.Folder113

end

-- From Challenge/Folder114.lean
@[expose] public section

namespace Grothendieck.Folder114

open CategoryTheory Limits Function

universe u

/-- A class of functors between small categories (objects and arrows in
`Type u`). -/
abbrev ClasseDeFoncteurs : Type (u + 1) :=
  ∀ ⦃A B : Type u⦄ [Category.{u} A] [Category.{u} B], (A ⥤ B) → Prop

/-- `W₀`: the functors inducing a bijection on connected components. -/
def W₀ : ClasseDeFoncteurs.{u} := fun _ _ _ _ F => Bijective F.mapConnectedComponents

/-- A small category `A` is `W`-aspheric when `A → e` is in `W`. -/
def Aspherique (W : ClasseDeFoncteurs.{u}) (A : Type u) [Category.{u} A] : Prop :=
  W (Functor.star.{u} A)

/-- The product `a × b` of two representables in `Â`, computed objectwise:
`(a × b)(c) = Hom(c, a) × Hom(c, b)`. -/
@[simps obj]
def produitRep {A : Type u} [Category.{u} A] (a b : A) : Aᵒᵖ ⥤ Type u where
  obj c := (c.unop ⟶ a) × (c.unop ⟶ b)
  map f := TypeCat.ofHom fun x => (f.unop ≫ x.1, f.unop ≫ x.2)

@[simp]
lemma produitRep_map_apply {A : Type u} [Category.{u} A] (a b : A) {c c' : Aᵒᵖ} (f : c ⟶ c')
    (x : (c.unop ⟶ a) × (c.unop ⟶ b)) :
    (produitRep a b).map f x = (f.unop ≫ x.1, f.unop ≫ x.2) := rfl

/-- `A_{/X}` for a presheaf `X`: the category of pairs `(c, yoneda c → X)`. -/
abbrev Tranche {A : Type u} [Category.{u} A] (X : Aᵒᵖ ⥤ Type u) : Type u :=
  CostructuredArrow yoneda X

/-- `A` is *totally `W`-aspheric*: `W`-aspheric, and `a × b` is `W`-aspheric
in `Â` (i.e. `A_{/a×b}` is `W`-aspheric) for all `a, b`. -/
def TotalementAspherique (W : ClasseDeFoncteurs.{u}) (A : Type u) [Category.{u} A] : Prop :=
  Aspherique W A ∧ ∀ a b : A, Aspherique W (Tranche (produitRep a b))

/-- Condition (iii) of Proposition 4: `A` non-empty, and `a × b` `0`-connected
(`A_{/a×b}` non-empty and connected) for all `a, b`. -/
def ConditionIII (A : Type u) [Category.{u} A] : Prop :=
  Nonempty A ∧ ∀ a b : A, IsConnected (Tranche (produitRep a b))

/-- Inclusion of classes of functors. -/
def Inclus (W W' : ClasseDeFoncteurs.{u}) : Prop :=
  ∀ ⦃A B : Type u⦄ [Category.{u} A] [Category.{u} B] (F : A ⥤ B), W F → W' F

/-- The argument of Proposition 4 for (ii) ⇒ (iii), with the inclusion
`W ⊆ W₀` it needs made a hypothesis. -/
theorem proposition4_ii_iii {W : ClasseDeFoncteurs.{u}} (hW : Inclus W W₀)
    (A : Type u) [Category.{u} A] (h : TotalementAspherique W A) : ConditionIII A := by
  sorry

end Grothendieck.Folder114

end

-- From Challenge/Folder115.lean
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

end

-- From Challenge/Folder118.lean
@[expose] public section

namespace Grothendieck.Folder118

open MulAction

variable (G : Type*) [Group G]

/-- `f : X → Y` is in `𝒲_A`, `A = BG`, read through the action groupoids: bijective on
orbits, and `Stab(f x) ⊆ Stab(x)` (the other inclusion always holds). -/
def IsWeq {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) : Prop :=
  (∀ y : Y, ∃ (x : X) (g : G), g • f x = y) ∧
  (∀ (x x' : X) (g : G), g • f x = f x' → ∃ h : G, h • x = x') ∧
  (∀ (x : X) (g : G), g • f x = f x → g • x = x)

/-- `X//G` is aspherical: non-empty, connected, with trivial automorphism groups. -/
def Aspherical (X : Type*) [MulAction G X] : Prop :=
  Nonempty X ∧ (∀ x y : X, ∃ g : G, g • x = y) ∧ ∀ (x : X) (g : G), g • x = x → g = 1

variable {G}

/-- The product of two maps of `G`-sets. -/
def prodHom {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] (f : X →[G] Y) (f' : X' →[G] Y') : X × X' →[G] Y × Y' where
  toFun p := (f p.1, f' p.2)
  map_smul' g p := by simp [map_smul]

/-- **The answer « Non » of page 35**, for `A = BG`, `G ≠ 1`: `𝒲_A` is stable under
products, but neither `A` nor `a × a` is aspherical. -/
theorem answer_page_35 [Nontrivial G] :
    (∀ {X Y X' Y' : Type} [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
      (f : X →[G] Y) (f' : X' →[G] Y'), IsWeq G f → IsWeq G f' → IsWeq G (prodHom f f')) ∧
    ¬ Aspherical G PUnit ∧ ¬ Aspherical G (G × G) := by
  sorry

end Grothendieck.Folder118

end

-- From Challenge/Folder120.lean
@[expose] public section

namespace Grothendieck.Folder120

open Function

universe u

/-- The axioms (M′1)–(M′4) of page 2 (with (M′) for finite index sets, page 4): a family
`M I ⊂ 𝔓(R^I)` of tame subsets, `u^* x = x ∘ u`. -/
structure TameModel (R : Type u) where
  /-- The tame subsets of `R^I`. -/
  M : (I : Type) → Set (Set (I → R))
  /-- (M′1) direct image by `u^*`. -/
  m1 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J) {A : Set (J → R)},
    A ∈ M J → (fun x : J → R => x ∘ u) '' A ∈ M I
  /-- (M′2) preimage by `u^*` for `u` surjective. -/
  m2 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J), Surjective u →
    ∀ {B : Set (I → R)}, B ∈ M I → (fun x : J → R => x ∘ u) ⁻¹' B ∈ M J
  /-- (M′3) cut of a tame subset by a preimage. -/
  m3 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J) {A : Set (J → R)}
    {B : Set (I → R)}, A ∈ M J → B ∈ M I → (fun x : J → R => x ∘ u) ⁻¹' B ∩ A ∈ M J
  /-- (M′4) products, `R^I × R^J = R^{I ⊔ J}`. -/
  m4 : ∀ {I J : Type} [Finite I] [Finite J] {A : Set (I → R)} {B : Set (J → R)},
    A ∈ M I → B ∈ M J → {x : I ⊕ J → R | x ∘ Sum.inl ∈ A ∧ x ∘ Sum.inr ∈ B} ∈ M (I ⊕ J)

/-- The graph over `X ⊂ R^I` of a family `F : R^I → R^K`, a subset of `R^{I ⊔ K}`. -/
def graphOn {R : Type u} {I K : Type} (X : Set (I → R)) (F : (I → R) → K → R) :
    Set (I ⊕ K → R) :=
  {y | y ∘ Sum.inl ∈ X ∧ ∀ k, y (Sum.inr k) = F (y ∘ Sum.inl) k}

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- A tame function on `X`: its graph over `X` is a tame subset of `R^{I ⊔ 1}`. -/
def IsTameFun {I : Type} (X : Set (I → R)) (f : (I → R) → R) : Prop :=
  graphOn X (fun x (_ : Unit) => f x) ∈ T.M (I ⊕ Unit)

/-- The tame points `R₀ = {c | {c} ∈ 𝓜₁}`. -/
def R0 : Set R := {c | {fun _ : Unit => c} ∈ T.M Unit}

/-- (M11) b) (page 20): `x - y` and `xy` are tame on every tame `A ⊂ R²`. -/
def RingOps [CommRing R] : Prop :=
  ∀ A ∈ T.M (Fin 2), T.IsTameFun A (fun z => z 0 - z 1) ∧ T.IsTameFun A (fun z => z 0 * z 1)

/-- (M11) in full, for a field (page 20): `0` and `1` tame points, b), and a tame set
containing the inverses of a tame `A ⊂ R^*`. -/
structure M11 [Field R] : Prop where
  zero_mem : (0 : R) ∈ T.R0
  one_mem : (1 : R) ∈ T.R0
  ringOps : T.RingOps
  inv : ∀ A ∈ T.M Unit, (∀ x ∈ A, x () ≠ 0) →
    ∃ B ∈ T.M Unit, ∀ x ∈ A, (fun _ => (x ())⁻¹) ∈ B

end TameModel

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- The Proposition under (M11) for a field, as the page states it. -/
theorem exists_separating_family_of_field [Field R] (h11 : T.M11) {I : Type} [Finite I]
    {X : Set (I → R)} (hX : X ∈ T.M I) {A : Type} [Finite A] (f : A → (I → R) → R)
    (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R) (he : ∀ a, e a ∈ T.R0) :
    ∃ (C : Type) (_ : Finite C) (h : C → (I → R) → R), (∀ c, T.IsTameFun X (h c)) ∧
      (∀ x, (∀ c, h c x = 0) ↔ ∀ a, f a x = e a) ∧
      ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y → ∃ c, h c x ≠ h c y := by
  sorry

end TameModel

end Grothendieck.Folder120

end

-- From Challenge/Folder121.lean
@[expose] public section

namespace Grothendieck.Folder121

open Set

variable {X : Type*} [TopologicalSpace X]

/-- `B` is rare in `Z`: no nonempty relatively open part of `Z` lies in `B`. -/
def Rare (B Z : Set X) : Prop := ∀ V, IsOpen V → V ∩ Z ⊆ B → V ∩ Z = ∅

/-- Conditions a) to e) of pages 3–5 on a family `F` of parts of `X`. -/
structure Tame (F : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F
  closure_mem : ∀ A ∈ F, closure A ∈ F
  dense_open : ∀ A ∈ F, ∃ G, IsOpen G ∧ G ∩ closure A ⊆ A ∧ closure A ⊆ closure (G ∩ closure A)
  dcc : ∀ A : ℕ → Set X, (∀ n, A n ∈ F ∧ IsClosed (A n)) →
    (∀ n, A (n + 1) ⊆ A n ∧ Rare (A (n + 1)) (A n)) → ∃ n, A n = ∅

variable {F : Set (Set X)}

/-- A finite cellular decomposition of `Z` (page 10): nonempty disjoint cells covering `Z`,
the closure of a cell a union of cells (1), distinct cells with distinct closures (2). -/
structure IsDecomp (Z : Set X) (P : Finset (Set X)) : Prop where
  nonempty : ∀ c ∈ P, c.Nonempty
  disjoint : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → Disjoint c d
  cover : ⋃ c ∈ P, c = Z
  frontier : ∀ c ∈ P, ∀ d ∈ P, (closure c ∩ d).Nonempty → d ⊆ closure c
  distinct : ∀ c ∈ P, ∀ d ∈ P, closure c = closure d → c = d

/-- Every member of `L` is a union of cells. -/
def Compat (L P : Finset (Set X)) : Prop := ∀ Y ∈ L, ∀ c ∈ P, c ⊆ Y ∨ Disjoint c Y

/-- An `F`-admissible decomposition of `Z` for which the members of `L` are unions of
cells. -/
def Good (F : Set (Set X)) (L : Finset (Set X)) (Z : Set X) (P : Finset (Set X)) : Prop :=
  IsDecomp Z P ∧ (∀ c ∈ P, c ∈ F) ∧ Compat L P

/-- `P` is coarser than `Q`: every cell of `Q` lies in a cell of `P`. -/
def Coarser (P Q : Finset (Set X)) : Prop := ∀ q ∈ Q, ∃ p ∈ P, q ⊆ p

/-- **Page 14.** Under a) to e), for every finite family `L ⊂ F` there is an `F`-admissible
cellular decomposition of `X` of which the members of `L` are unions of cells, and among them
one coarser than all the others. -/
theorem page14 (hF : Tame F) (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, Good F L univ P ∧ ∀ Q, Good F L univ Q → Coarser P Q := by
  sorry

end Grothendieck.Folder121

end

-- From Challenge/Folder123Kostant.lean
@[expose] public section

namespace Grothendieck.Folder123Kostant

/-- `card(W)`, `h`, `z` for a simple type: `(|W|, h, z)`. -/
def dataA (n : ℕ) : ℕ × ℕ × ℕ := ((n + 1).factorial, n + 1, n + 1)

def dataB (n : ℕ) : ℕ × ℕ × ℕ := (2 ^ n * n.factorial, 2 * n, 2)

def dataG2 : ℕ × ℕ × ℕ := (12, 6, 1)

/-- The announced number of classes. -/
def number (d : ℕ × ℕ × ℕ) : ℕ := d.1 ^ 2 / (d.2.1 * d.2.2 * Nat.totient d.2.1)

/-- The hand checks of the reading: `A₁`, `A₂`, `B₂`, `G₂` give 1, 2, 4, 12. -/
theorem small_cases :
    number (dataA 1) = 1 ∧ number (dataA 2) = 2 ∧ number (dataB 2) = 4 ∧ number dataG2 = 12 := by
  sorry

end Grothendieck.Folder123Kostant

end

-- From Challenge/Folder125.lean
@[expose] public section

namespace Grothendieck.Folder125

section FeuilletIII18

variable {R : Type*} [CommRing R]

/-- **Feuillet 3 (III-18), affine form.** `R` Noetherian, `B` of finite type,
`u : Rⁿ → B` an isomorphism on the germs at `𝔭`: then `u` is an isomorphism over
a neighbourhood `D(f)` of `𝔭`. -/
theorem lemme_III18 [IsNoetherianRing R] {B : Type*} [AddCommGroup B] [Module R B]
    [Module.Finite R B] {n : ℕ} (u : (Fin n → R) →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) := by
  sorry

end FeuilletIII18

end Grothendieck.Folder125

end

-- From Challenge/Folder128.lean
@[expose] public section

open TensorProduct

namespace Grothendieck.Folder128.Descent

universe u

section Defs

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A descent datum on an `S`-module `E` relative to `R → S` (Grothendieck, page 4), written as
a comodule over the coring `S ⊗_R S`: an `S`-linear `ψ : E → S ⊗_R E` (`ψ(e) = φ(1 ⊗ e)` for
the gluing isomorphism `φ`), with counit `Σ bᵢ eᵢ = e` and the cocycle condition. -/
structure DescentDatum (E : Type u) [AddCommGroup E] [Module S E] [Module R E]
    [IsScalarTower R S E] where
  /-- The coaction `e ↦ Σ bᵢ ⊗ eᵢ`. -/
  ψ : E →ₗ[S] S ⊗[R] E
  /-- Counit: `Σ bᵢ eᵢ = e`. -/
  counit : ∀ e, LinearMap.liftBaseChange S (LinearMap.id : E →ₗ[R] E) (ψ e) = e
  /-- Cocycle: `Σ bᵢ ⊗ ψ(eᵢ) = Σ bᵢ ⊗ 1 ⊗ eᵢ`. -/
  coassoc : ∀ e, (ψ.restrictScalars R).lTensor S (ψ e) =
    (TensorProduct.mk R S E 1).lTensor S (ψ e)

variable {R S}

namespace DescentDatum

variable {E : Type u} [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]

/-- The invariants `{e | ψ(e) = 1 ⊗ e}` (the `H⁰` of the descent complex). -/
def invariants (d : DescentDatum R S E) : Submodule R E :=
  LinearMap.eqLocus (d.ψ.restrictScalars R) (TensorProduct.mk R S E 1)

/-- The datum is effective: its invariants `E₀` are flat and `S ⊗_R E₀ → E` is bijective, so the
datum is isomorphic to the canonical one on `S ⊗_R E₀`. -/
def IsEffective (d : DescentDatum R S E) : Prop :=
  Module.Flat R d.invariants ∧
    Function.Bijective (LinearMap.liftBaseChange S d.invariants.subtype)

end DescentDatum

variable (R S) in
/-- The canonical descent datum on `S ⊗_R M`, `b ⊗ m ↦ b ⊗ 1 ⊗ m`. -/
noncomputable def canonical (M : Type u) [AddCommGroup M] [Module R M] :
    DescentDatum R S (S ⊗[R] M) where
  ψ := (TensorProduct.mk R S M 1).baseChange S
  counit x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy]
  coassoc x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp
    | add x y hx hy => simp only [map_add, hx, hy]

variable (R S) in
/-- `Spec S → Spec R` is a descent morphism for flat modules: for `M` flat, `M → S ⊗_R M` is
injective with image the invariants of the canonical datum (`M ≅ H⁰(S/R, M)`). -/
def IsDescentFlat : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Flat R M],
    Function.Injective (TensorProduct.mk R S M 1) ∧
      (canonical R S M).invariants ≤ LinearMap.range (TensorProduct.mk R S M 1)

variable (R S) in
/-- `Spec S → Spec R` is an effective descent morphism for flat modules: a descent morphism, and
every descent datum on a flat `S`-module is effective. -/
def IsEffectiveDescentFlat : Prop :=
  IsDescentFlat R S ∧
    ∀ (E : Type u) [AddCommGroup E] [Module S E] [Module R E] [IsScalarTower R S E]
      [Module.Flat S E] (d : DescentDatum R S E), d.IsEffective

end Defs

section Reduction

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]

variable (S) in
/-- `I` is an ideal of `A` mapped injectively onto an ideal of `S` (Grothendieck, page 1): `I`
lies in the conductor, and `A → S`, `A/I → S/IS` is a Milnor square. -/
structure IsConductorIdeal (I : Ideal A) : Prop where
  inj : ∀ x ∈ I, algebraMap A S x = 0 → x = 0
  ideal : ∀ x ∈ I, ∀ b : S, ∃ y ∈ I, b * algebraMap A S x = algebraMap A S y

variable {I : Ideal A}

variable (I) {N : Type u} [AddCommGroup N] [Module A N]
  {M₀ : Type u} [AddCommMonoid M₀] [Module (A ⧸ I) M₀] [Module A M₀]
  [IsScalarTower A (A ⧸ I) M₀]

variable {I}

end Reduction

section Main

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {I : Ideal A}
  {E : Type u} [AddCommGroup E] [Module S E] [Module A E] [IsScalarTower A S E]

/-- **Folder 128, Cor. 1** (Grothendieck, page 7). Let `I` be a nilpotent ideal of `A` mapped
isomorphically onto an ideal of `S` (`I` in the conductor). If `Spec S/IS → Spec A/I` is an
effective descent morphism for flat modules, so is `Spec S → Spec A`. -/
theorem isEffectiveDescentFlat_of_quotient (h : IsConductorIdeal S I) (hI : IsNilpotent I)
    (h₀ : IsEffectiveDescentFlat (A ⧸ I) (S ⧸ I.map (algebraMap A S))) :
    IsEffectiveDescentFlat A S := by
  sorry

end Main

end Grothendieck.Folder128.Descent

end

-- From Challenge/Folder133.lean
@[expose] public section

namespace Grothendieck.Folder133

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G] (N N' : Subgroup G) [N.Normal] [N'.Normal]

/-- The inverse image in `G` of `ℨ = [Cent(K)/(N′/π₁)] ∩ Ker Θ`, `K = G/π₁`,
`π₁ = N ∩ N′` (page 46): the elements central modulo `π₁` that centralise `N`. -/
def zbar : Subgroup G :=
  (center (G ⧸ (N ⊓ N'))).comap (QuotientGroup.mk' (N ⊓ N')) ⊓ centralizer (N : Set G)

/-- `ℨ = zbar ⧸ N′` (page 46). -/
abbrev Zfrak := zbar N N' ⧸ N'.subgroupOf (zbar N N')

variable {N N'}

theorem mem_zbar {z : G} :
    z ∈ zbar N N' ↔ (∀ g : G, ⁅g, z⁆ ∈ N ⊓ N') ∧ ∀ n ∈ N, n * z = z * n := by
  rw [zbar, mem_inf, mem_comap, mem_centralizer_iff]
  refine and_congr ⟨fun h g => ?_, fun h => mem_center_iff.mpr fun x => ?_⟩ Iff.rfl
  · exact (QuotientGroup.eq_one_iff _).mp <| (map_commutatorElement (QuotientGroup.mk' _) g z).trans
      (commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h _))
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact commutatorElement_eq_one_iff_mul_comm.mp <|
      (map_commutatorElement (QuotientGroup.mk' _) g z).symm.trans
        ((QuotientGroup.eq_one_iff _).mpr (h g))

/-- A central element commutes with everything, written in the order used below. -/
theorem central_comm {H : Type*} [Group H] {c : H} (hc : c ∈ center H) (x : H) :
    c * x = x * c :=
  (mem_center_iff.mp hc x).symm

/-- Multiplying the second argument of a commutator by a central element does not change it. -/
theorem comm_mul_central {H : Type*} [Group H] {c : H} (hc : c ∈ center H) (g z : H) :
    ⁅g, z * c⁆ = ⁅g, z⁆ := by
  simp only [commutatorElement_def]
  calc g * (z * c) * g⁻¹ * (z * c)⁻¹ = g * z * (c * g⁻¹) * c⁻¹ * z⁻¹ := by group
    _ = g * z * (g⁻¹ * c) * c⁻¹ * z⁻¹ := by rw [central_comm hc]
    _ = g * z * g⁻¹ * z⁻¹ := by group

section Centre

variable (hN' : N' ≤ center G)

include hN'

theorem comm_mem_center {z : G} (hz : z ∈ zbar N N') (g : G) : ⁅g, z⁆ ∈ center G :=
  hN' (mem_inf.mp ((mem_zbar.mp hz).1 g)).2

theorem comm_mul_left {z : G} (hz : z ∈ zbar N N') (g h : G) :
    ⁅g * h, z⁆ = ⁅g, z⁆ * ⁅h, z⁆ := by
  have hc := comm_mem_center hN' hz h
  calc ⁅g * h, z⁆ = g * (⁅h, z⁆ * (z * g⁻¹ * z⁻¹)) := by
        simp only [commutatorElement_def]; group
    _ = ⁅h, z⁆ * (g * z * g⁻¹ * z⁻¹) := by
        rw [← mul_assoc, ← central_comm hc g]; group
    _ = ⁅h, z⁆ * ⁅g, z⁆ := by rw [commutatorElement_def g z]
    _ = ⁅g, z⁆ * ⁅h, z⁆ := central_comm hc _

/-- For `z ∈ zbar`, `g ↦ ⁅g, z⁆` as a homomorphism `G →* π₁`. -/
def commHom (z : zbar N N') : G →* ↥(N ⊓ N') where
  toFun g := ⟨⁅g, z⁆, (mem_zbar.mp z.2).1 g⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; exact comm_mul_left hN' z.2 g h

theorem le_ker_commHom (z : zbar N N') : N ⊔ N' ≤ (commHom hN' z).ker := by
  refine sup_le (fun n hn => ?_) (fun n hn => ?_) <;> rw [MonoidHom.mem_ker] <;>
    apply Subtype.ext <;> show ⁅n, (z : G)⁆ = 1 <;> rw [commutatorElement_eq_one_iff_mul_comm]
  · exact (mem_zbar.mp z.2).2 n hn
  · exact (mem_center_iff.mp (hN' hn) z).symm

/-- `φ_G(z) : π₀ → π₁`, `π₀ = G/NN′`: the commutator with `z`, on `π₀`. -/
def phi (z : zbar N N') : G ⧸ (N ⊔ N') →* ↥(N ⊓ N') :=
  QuotientGroup.lift _ (commHom hN' z) (le_ker_commHom hN' z)

theorem phi_eq_of_rel {z w : zbar N N'} (h : z⁻¹ * w ∈ N'.subgroupOf (zbar N N')) :
    phi hN' z = phi hN' w := by
  refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun g => Subtype.ext ?_)
  show ⁅g, (z : G)⁆ = ⁅g, (w : G)⁆
  have hc : (z : G)⁻¹ * w ∈ center G := hN' (by simpa [mem_subgroupOf] using h)
  rw [show (w : G) = z * ((z : G)⁻¹ * w) by group, comm_mul_central hc]

/-- `Ψ_G : ℨ → Hom(π₀, π₁)` (page 46). -/
def Psi : Zfrak N N' → (G ⧸ (N ⊔ N') →* ↥(N ⊓ N')) :=
  fun a => Quotient.liftOn' a (phi hN') fun _ _ h =>
    phi_eq_of_rel hN' (QuotientGroup.leftRel_apply.mp h)

/-- **Page 46.** `N′ = Cent(G)` if and only if `Ψ_G` is injective. -/
theorem injective_Psi_iff : Function.Injective (Psi (N := N) hN') ↔ N' = center G := by
  sorry

end Centre

end Grothendieck.Folder133

end

-- From Challenge/Folder136.lean
@[expose] public section

namespace Grothendieck.Folder136

/-- **Théorème 1 (p. 22).** If `binom(j, i)(x_j − x_i) = 0` for all `j > i ≥ N` in an
abelian group, then `x_j = x_N` for every `j ≥ N`. -/
theorem binomial_constant {A : Type*} [AddCommGroup A] (x : ℕ → A) (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (x j - x i) = 0) :
    ∀ j, N ≤ j → x j = x N := by
  sorry

end Grothendieck.Folder136

open TensorProduct Coalgebra WithConv Polynomial Finset

end

-- From Challenge/Folder137.lean
@[expose] public section

namespace Grothendieck.Folder137.Perfect

open CategoryTheory Limits

universe u

noncomputable section

variable (k : Type u) [CommRing k]

/-- The support of the disc `ℂⁿ`: `k` in degrees `n` and `n + 1`, `0` elsewhere. -/
def discS (n m : ℕ) : Submodule k k := if m = n ∨ m = n + 1 then ⊤ else ⊥

lemma mem_discS_of_eq (n m : ℕ) (h : m = n ∨ m = n + 1) (x : k) : x ∈ discS k n m := by
  simp [discS, h]

/-- The differential of the disc, the identity of `k` from degree `n + 1` to degree `n`. -/
def discD (n m : ℕ) : ModuleCat.of k (discS k n (m + 1)) ⟶ ModuleCat.of k (discS k n m) :=
  ModuleCat.ofHom (LinearMap.codRestrict (discS k n m)
    ((if m = n then LinearMap.id else 0) ∘ₗ (discS k n (m + 1)).subtype) (fun x => by
      by_cases h : m = n
      · exact mem_discS_of_eq k n m (Or.inl h) _
      · simp [h]))

@[simp]
lemma discD_apply (n m : ℕ) (x : ModuleCat.of k (discS k n (m + 1))) :
    Subtype.val ((discD k n m).hom x) = if m = n then Subtype.val x else 0 := by
  by_cases h : m = n <;> simp [discD, h]

/-- The disc `ℂⁿ` (p. 39): the chain complex `k → k`, identity, in degrees `n + 1`, `n`. -/
noncomputable abbrev disc (n : ℕ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun m => ModuleCat.of k (discS k n m)) (discD k n) (fun m => by
    ext x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, discD_apply, discD_apply]
    split_ifs <;> first | rfl | omega)

/-- The value in `k` of an element of a component of a disc. -/
def dv {n m : ℕ} (x : (disc k n).X m) : k := (show discS k n m from x).1

@[simp]
lemma disc_d_apply (n m : ℕ) (x : (disc k n).X (m + 1)) :
    dv k (((disc k n).d (m + 1) m).hom x) = if m = n then dv k x else 0 := by
  rw [show (disc k n).d (m + 1) m = discD k n m by simp [disc]]
  exact discD_apply k n m x

@[simp]
lemma dv_discD (n m : ℕ) (x : (disc k n).X (m + 1)) :
    dv k ((discD k n m).hom x) = if m = n then dv k x else 0 := discD_apply k n m x

@[simp] lemma dv_smul {n m : ℕ} (c : k) (x : (disc k n).X m) : dv k (c • x) = c * dv k x := rfl

@[simp] lemma dv_add {n m : ℕ} (x y : (disc k n).X m) : dv k (x + y) = dv k x + dv k y := rfl

@[simp] lemma dv_zero {n m : ℕ} : dv k (0 : (disc k n).X m) = 0 := rfl

@[simp] lemma dv_neg {n m : ℕ} (x : (disc k n).X m) : dv k (-x) = - dv k x := rfl

variable {k}

variable (k) in
/-- The generator `1` of the disc `ℂⁿ`, in degree `n + 1`. -/
def one (n : ℕ) : (disc k n).X (n + 1) := ⟨1, mem_discS_of_eq k n (n + 1) (Or.inr rfl) 1⟩

@[simp] lemma dv_one (n : ℕ) : dv k (one k n) = 1 := rfl

/-- Proposition 1 (p. 40), the endomorphisms of a disc: `End(ℂⁿ) = k · id`. -/
lemma disc_endo {n : ℕ} (f : disc k n ⟶ disc k n) :
    f = dv k ((f.f (n + 1)).hom (one k n)) • 𝟙 _ := by
  sorry

end

end Grothendieck.Folder137.Perfect

end

-- From Challenge/Folder140_1.lean
@[expose] public section

namespace Grothendieck.Folder140_1

open groupCohomology

section General

variable {G : Type} [Group G]

/-- The `ℤ`-linear representation of `G` on an abelian group with a distributive action. -/
abbrev R (G M : Type) [Group G] [AddCommGroup M] [DistribMulAction G M] : Rep ℤ G :=
  Rep.ofDistribMulAction ℤ G M

variable {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N]
  [DistribMulAction G N]

variable (G M) in
/-- The 1-cocycles `f(gh) = g f(h) + f(g)`. -/
def Z1 : AddSubgroup (G → M) where
  carrier := {f | IsCocycle₁ f}
  add_mem' {f f'} hf hf' g h := by
    simp only [Pi.add_apply, hf g h, hf' g h, smul_add]; abel
  zero_mem' g h := by simp
  neg_mem' {f} hf g h := by simp only [Pi.neg_apply, hf g h, smul_neg]; abel

variable (G M) in
/-- The 1-coboundaries `g ↦ g m - m`, inside the cocycles. -/
def B1 : AddSubgroup (Z1 G M) where
  carrier := {f | IsCoboundary₁ (f : G → M)}
  add_mem' {f f'} := fun ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun g => by
    change g • (x + x') - (x + x') = (f : G → M) g + (f' : G → M) g
    rw [smul_add, ← hx, ← hx']
    abel⟩
  zero_mem' := ⟨0, fun g => by simp⟩
  neg_mem' {f} := fun ⟨x, hx⟩ => ⟨-x, fun g => by
    change g • (-x) - (-x) = -(f : G → M) g
    rw [smul_neg, ← hx]
    abel⟩

variable (G M) in
/-- `Z¹ / B¹`. -/
abbrev Q := Z1 G M ⧸ B1 G M

/-- Mathlib's cocycles are these cocycles. -/
def cocyclesEquiv : cocycles₁ (R G M) ≃+ Z1 G M where
  toFun f := ⟨f.1, isCocycle₁_of_mem_cocycles₁ _ f.2⟩
  invFun f := ⟨f.1, (cocyclesOfIsCocycle₁ (k := ℤ) f.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (G M) in
/-- `H¹(G, M)` (Mathlib's, for the representation on `M`) is cocycles modulo coboundaries. -/
noncomputable def H1Equiv : Q G M ≃+ H1 (R G M) :=
  let ψ : Z1 G M →+ H1 (R G M) :=
    (H1π (R G M)).hom.toAddMonoidHom.comp (cocyclesEquiv (G := G) (M := M)).symm.toAddMonoidHom
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (H1π (R G M))).1 inferInstance y
    exact ⟨cocyclesEquiv x, by simpa [ψ] using hx⟩
  have hk : ψ.ker = B1 G M := by
    ext f
    change (H1π (R G M)) (cocyclesEquiv.symm f) = 0 ↔ IsCoboundary₁ (f : G → M)
    rw [H1π_eq_zero_iff]
    exact ⟨isCoboundary₁_of_mem_coboundaries₁ _,
      fun h => (coboundariesOfIsCoboundary₁ (k := ℤ) h).2⟩
  (QuotientAddGroup.quotientAddEquivOfEq hk.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ)

variable {A : Type} [AddCommGroup A] [DistribMulAction G A]

end General

/-- `𝔖₃ = 𝔖_J`, `J = {0, 1, 2}`. -/
abbrev G3 := Equiv.Perm (Fin 3)

/-- `V(J) = Ker(ℤ^J → ℤ)`, the divisors of the units of `U_{0,3}`. -/
def VJ : AddSubgroup (Fin 3 → ℤ) where
  carrier := {x | ∑ j, x j = 0}
  add_mem' {x y} hx hy := by simp_all [Finset.sum_add_distrib]
  zero_mem' := by simp
  neg_mem' {x} hx := by simp_all

lemma sum_perm (σ : G3) (x : Fin 3 → ℤ) : ∑ j, x (σ⁻¹ j) = ∑ j, x j :=
  Equiv.sum_comp σ⁻¹ x

/-- `𝔖₃` permutes the coordinates: `(σ x)_j = x_{σ⁻¹ j}`. -/
instance : DistribMulAction G3 VJ where
  smul σ x := ⟨fun j => (x : Fin 3 → ℤ) (σ⁻¹ j), (sum_perm σ x).trans x.2⟩
  one_smul x := rfl
  mul_smul σ τ x := by ext j; rfl
  smul_zero σ := rfl
  smul_add σ x y := rfl

@[simp] lemma smul_VJ (σ : G3) (x : VJ) (j : Fin 3) :
    ((σ • x : VJ) : Fin 3 → ℤ) j = (x : Fin 3 → ℤ) (σ⁻¹ j) := rfl

/-- The units of a ring `k` (the units of the base `S`), written additively, with the trivial
action of `𝔖₃`. -/
def Triv (k : Type) [CommRing k] := Additive kˣ

instance (k : Type) [CommRing k] : AddCommGroup (Triv k) :=
  inferInstanceAs (AddCommGroup (Additive kˣ))

variable {k : Type} [CommRing k]

/-- The coefficients of `sgnExp σ`: `1` at `0` when `σ⁻¹(∞) = 1`, at `1` when `σ⁻¹(∞) = 0`. -/
def wt (σ : G3) (j : Fin 3) : ℤ := if σ⁻¹ 2 = 1 ∧ j = 0 ∨ σ⁻¹ 2 = 0 ∧ j = 1 then 1 else 0

/-- The parity of the constant that appears when `λ^a (1 − λ)^b`, `v = (a, b, −a − b)`, is
composed with the substitution `h` inducing `σ⁻¹` on `0, 1, ∞`: `hλ` carries a sign when
`h(∞) = 1`, and `1 − hλ` when `h(∞) = 0`. -/
def sgnExp (σ : G3) (v : VJ) : ℤ := ∑ j, wt σ j * (v : Fin 3 → ℤ) j

lemma sgnExp_add (σ : G3) (v w : VJ) : sgnExp σ (v + w) = sgnExp σ v + sgnExp σ w := by
  simp [sgnExp, mul_add, Finset.sum_add_distrib]

lemma wt_key : ∀ σ τ : G3, ∀ j, (wt (σ * τ) j - wt τ j - wt σ (τ j) -
    (wt (σ * τ) 0 - wt τ 0 - wt σ (τ 0))) % 2 = 0 := by decide

lemma sgnExp_mul (σ τ : G3) (v : VJ) :
    2 ∣ sgnExp (σ * τ) v - (sgnExp τ v + sgnExp σ (τ • v)) := by
  have hv : ∑ j, (v : Fin 3 → ℤ) j = 0 := v.2
  have e : sgnExp σ (τ • v) = ∑ j, wt σ (τ j) * (v : Fin 3 → ℤ) j := by
    simp only [sgnExp, smul_VJ]
    rw [← Equiv.sum_comp τ]
    simp
  obtain ⟨t1, h1⟩ := Int.dvd_of_emod_eq_zero (wt_key σ τ 1)
  obtain ⟨t2, h2⟩ := Int.dvd_of_emod_eq_zero (wt_key σ τ 2)
  rw [e]
  simp only [sgnExp, Fin.sum_univ_three] at hv ⊢
  exact ⟨t1 * (v : Fin 3 → ℤ) 1 + t2 * (v : Fin 3 → ℤ) 2, by
    linear_combination (v : Fin 3 → ℤ) 1 * h1 + (v : Fin 3 → ℤ) 2 * h2 +
      (wt (σ * τ) 0 - wt τ 0 - wt σ (τ 0)) * hv⟩

@[simp] lemma sgnExp_zero (σ : G3) : sgnExp σ 0 = 0 := by simp [sgnExp]

@[simp] lemma sgnExp_one (v : VJ) : sgnExp 1 v = 0 := by simp [sgnExp, wt]

/-- The units of `U_{0,3} = Spec k[λ, 1/λ, 1/(1 − λ)]`, written additively: `c λ^a (1 − λ)^b`
is `(c, (a, b, −a − b))`, the second component its divisor on `0, 1, ∞`. -/
def Units3 (k : Type) [CommRing k] := Triv k × VJ

instance : AddCommGroup (Units3 k) := inferInstanceAs (AddCommGroup (Triv k × VJ))

namespace Units3

/-- The unit `c λ^a (1 − λ)^b`, `v = (a, b, −a − b)`. -/
def mk (c : Triv k) (v : VJ) : Units3 k := (c, v)

/-- The constant. -/
def cst (x : Units3 k) : Triv k := Prod.fst (β := VJ) x

/-- The divisor. -/
def dv (x : Units3 k) : VJ := Prod.snd (α := Triv k) x

@[ext] lemma ext {x y : Units3 k} (h1 : x.cst = y.cst) (h2 : x.dv = y.dv) : x = y :=
  Prod.ext h1 h2

@[simp] lemma cst_mk (c : Triv k) (v : VJ) : (mk c v).cst = c := rfl

@[simp] lemma dv_mk (c : Triv k) (v : VJ) : (mk c v).dv = v := rfl

@[simp] lemma cst_add (x y : Units3 k) : (x + y).cst = x.cst + y.cst := rfl

@[simp] lemma dv_add (x y : Units3 k) : (x + y).dv = x.dv + y.dv := rfl

@[simp] lemma cst_sub (x y : Units3 k) : (x - y).cst = x.cst - y.cst := rfl

@[simp] lemma dv_sub (x y : Units3 k) : (x - y).dv = x.dv - y.dv := rfl

@[simp] lemma cst_zero : (0 : Units3 k).cst = 0 := rfl

@[simp] lemma dv_zero : (0 : Units3 k).dv = 0 := rfl

@[simp] lemma cst_zsmul (m : ℤ) (x : Units3 k) : (m • x).cst = m • x.cst := rfl

@[simp] lemma dv_zsmul (m : ℤ) (x : Units3 k) : (m • x).dv = m • x.dv := rfl

end Units3

open Units3

/-- `(-1)^s`, in `k^*` written additively. -/
def negPow (s : ℤ) : Triv k := Additive.ofMul ((-1 : kˣ) ^ s)

lemma negPow_add (s t : ℤ) : negPow (k := k) (s + t) = negPow s + negPow t := by
  rw [negPow, zpow_add]; rfl

@[simp] lemma negPow_zero : negPow (k := k) 0 = 0 := by rw [negPow, zpow_zero]; rfl

lemma negPow_eq_zero {s : ℤ} (h : 2 ∣ s) : negPow (k := k) s = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [negPow, zpow_mul, show ((-1 : kˣ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow]; rfl

lemma negPow_congr {s t : ℤ} (h : 2 ∣ s - t) : negPow (k := k) s = negPow t := by
  rw [show s = s - t + t by ring, negPow_add, negPow_eq_zero h, zero_add]

/-- The anharmonic action: `σ` sends `f` to `f ∘ h`, `h` the substitution inducing `σ⁻¹` on
`0, 1, ∞`; on the divisor it permutes the coordinates, on the constant it multiplies by
`(-1)^{sgnExp σ v}` (`ev_smul`). -/
instance : DistribMulAction G3 (Units3 k) where
  smul σ x := mk (x.cst + negPow (sgnExp σ x.dv)) (σ • x.dv)
  one_smul x := Units3.ext (show x.cst + negPow (sgnExp 1 x.dv) = x.cst by simp)
    (one_smul G3 x.dv)
  mul_smul σ τ x := Units3.ext (by
    change x.cst + _ = x.cst + _ + _
    rw [add_assoc, ← negPow_add, negPow_congr (sgnExp_mul σ τ x.dv)]; rfl) (mul_smul σ τ x.dv)
  smul_zero σ := Units3.ext (show (0 : Units3 k).cst + negPow (sgnExp σ 0) = 0 by simp)
    (smul_zero σ)
  smul_add σ x y := Units3.ext (by
    change x.cst + y.cst + negPow (sgnExp σ (x.dv + y.dv)) = x.cst + _ + (y.cst + _)
    rw [sgnExp_add, negPow_add]; abel) (smul_add σ x.dv y.dv)

@[simp] lemma cst_smul (σ : G3) (x : Units3 k) :
    (σ • x).cst = x.cst + negPow (sgnExp σ x.dv) := rfl

@[simp] lemma dv_smul (σ : G3) (x : Units3 k) : (σ • x).dv = σ • x.dv := rfl

/-- The sign of a permutation, in `k^*`. -/
def sgnK (σ : G3) : Triv k :=
  Additive.ofMul (Units.map (Int.castRingHom k).toMonoidHom (Equiv.Perm.sign σ))

/-- The point `∞`. -/
def e2 : Fin 3 → ℤ := fun j => if j = 2 then 1 else 0

/-- The divisor `2[∞] − 2[σ(∞)]`. -/
def tanV (σ : G3) : VJ := ⟨fun j => 2 * (e2 j - e2 (σ⁻¹ j)), by
  change ∑ j, 2 * (e2 j - e2 (σ⁻¹ j)) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_perm σ e2, sub_self, mul_zero]⟩

lemma sgnExp_tanV (σ τ : G3) : 2 ∣ sgnExp σ (tanV τ) :=
  Finset.dvd_sum fun _ _ => Dvd.dvd.mul_left (dvd_mul_right 2 _) _

/-- The tangent cocycle `σ ↦ (h⁻¹)′(λ)`, `h` inducing `σ` on `0, 1, ∞`: its constant is the
sign of `σ` and its divisor `2[∞] − 2[σ(∞)]` (`ev_tan`). -/
def tan : Z1 G3 (Units3 k) :=
  ⟨fun σ => mk (sgnK σ) (tanV σ), fun σ τ => Units3.ext (by
    simp only [cst_add, cst_smul, cst_mk, dv_mk, negPow_eq_zero (sgnExp_tanV σ τ), add_zero]
    rw [add_comm, sgnK, map_mul, map_mul]; rfl)
    (by ext j; simp [tanV, mul_inv_rev]; ring)⟩

/-- The lower bound of page 24, with the bound of page 22: for a domain `k` with `2 ≠ 0`,
`H¹(𝔖₃, O(U_{0,3})^*) ≃ ℤ/6`, generated by the tangent class. -/
theorem H1_units [IsDomain k] (h2 : (2 : k) ≠ 0) :
    Nat.card (H1 (R G3 (Units3 k))) = 6 ∧
      addOrderOf (H1Equiv G3 (Units3 k) (QuotientAddGroup.mk tan)) = 6 ∧
      Nonempty (H1 (R G3 (Units3 k)) ≃+ ZMod 6) := by
  sorry

end Grothendieck.Folder140_1

end

-- From Challenge/Folder145.lean
@[expose] public section

namespace Grothendieck.Folder145

open DihedralGroup

/-- A profinite integer, as a family of residues: `p n ∈ ZMod n` for `n ≠ 0`, compatible
under reduction. (The value at `n = 0` plays no role.) -/
def Compatible (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ m n : ℕ, n ≠ 0 → ∀ h : m ∣ n, ZMod.castHom h (ZMod m) (p n) = p m

/-- `x ^ p` for `p ∈ ℤ̂` in a finite group: the power by the residue of `p` modulo the
order of the group. -/
def hatPow {G : Type*} [Group G] [Fintype G] (p : ∀ n : ℕ, ZMod n) (x : G) : G :=
  x ^ (p (Fintype.card G)).val

/-- Relation (14) of page 35, `l_∞^p l₁^p l₀^p = 1` under `l_∞ l₁ l₀ = 1`, read in every
finite quotient of the free profinite group on `l₀, l₁`. -/
def Rel14 (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (x y z : G),
    z * y * x = 1 → hatPow p z * hatPow p y * hatPow p x = 1

/-- The page's form: `p` a unit of `ℤ̂` (each residue a unit). -/
theorem rel14_unit_iff (p : ∀ n : ℕ, ZMod n) (hp : Compatible p)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (p n)) :
    Rel14 p ↔ ∀ n : ℕ, n ≠ 0 → p n = 1 := by
  sorry

end Grothendieck.Folder145

end

-- From Challenge/Folder146.lean
@[expose] public section

namespace Grothendieck.Folder146

variable {K : Type*} [Field K]

/-- The substitutions. -/
def anh : Fin 6 → K → K
  | 0 => fun x => x
  | 1 => fun x => 1 / x
  | 2 => fun x => 1 - x
  | 3 => fun x => x / (x - 1)
  | 4 => fun x => 1 / (1 - x)
  | 5 => fun x => (x - 1) / x

/-- Their derivatives `g′(λ)`: the action on the tangent line `L₄` at the fourth point. -/
def der : Fin 6 → K → K
  | 0 => fun _ => 1
  | 1 => fun x => -1 / x ^ 2
  | 2 => fun _ => -1
  | 3 => fun x => -1 / (x - 1) ^ 2
  | 4 => fun x => 1 / (1 - x) ^ 2
  | 5 => fun x => 1 / x ^ 2

/-- `U = ℙ¹ ∖ {0, 1, ∞}`. -/
def U (x : K) : Prop := x ≠ 0 ∧ x ≠ 1

/-- No smaller power is a coboundary, even among all nowhere-zero functions on `U(K)`: if
`g′(λ)^m = h(gλ)/h(λ)` for all `g` and `λ`, then `6 ∣ m`. At `λ = −1`, fixed by `1/λ` with
derivative `−1`, and at a root `ζ` of `ζ² − ζ + 1`, fixed by `1/(1 − λ)` with derivative `ζ²`,
a primitive cube root of unity. -/
theorem six_dvd (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {ζ : K} (hζ : ζ ^ 2 - ζ + 1 = 0)
    (m : ℤ) (h : K → K) (hh : ∀ x, U x → h x ≠ 0)
    (hc : ∀ a x, U x → der a x ^ m = h (anh a x) / h x) : 6 ∣ m := by
  sorry

variable {α : Type*} {n : ℕ} {V : α → Prop} {act : Fin n → α → α} {c : Fin n → α → K}

end Grothendieck.Folder146

end

-- From Challenge/Folder147.lean
@[expose] public section

namespace Grothendieck.Folder147

variable {K : Type*} [Field K] [CharZero K]

/-- Formula (80) of folder 147, page 63, from the stratification of the `j`-line. -/
theorem class_M11 (L z₂ z₃ : K) :
    (1 / 2) * (L - 2 + z₂ + z₃) + (1 / 4) * (1 - z₂ - z₃) + (1 / 6) * (1 - z₂ - z₃)
        + (1 / 24) * z₂ + (1 / 12) * z₃
      = (1 / 2) * (L - 1) - 1 / 12 + (1 / 8) * z₂ + (1 / 6) * z₃ := by
  sorry

end Grothendieck.Folder147

end

-- From Challenge/Folder148.lean
@[expose] public section

open Set Filter Topology

namespace Grothendieck.Folder148

/-- A circle `ℝ/ℤ` with `r` marked points, given by its lifted marked points: a strictly
increasing `pt : ℤ → ℝ` with `pt (k + r) = pt k + 1`. The marked point `pt k` has label
`k mod r` in the torsor `ℤ/r`. -/
structure Marking (r : ℕ) where
  /-- The lifted marked points. -/
  pt : ℤ → ℝ
  strictMono : StrictMono pt
  periodic : ∀ k, pt (k + r) = pt k + 1

variable {r : ℕ}

end Grothendieck.Folder148

open scoped ContinuousMap

namespace Grothendieck.Folder148

variable {r : ℕ}

/-- The orientation-reversing homeomorphisms `a → a'` of the circle `AddCircle 1` respecting the
markings through the anti-isomorphism `k ↦ c - k`: bijective continuous maps (homeomorphisms,
the circle being compact) admitting a strictly antitone continuous lift, sending the marked
point `p k` to `q (c - k)`. -/
def circleGluings (P Q : Marking r) (c : ℤ) : Set C(UnitAddCircle, UnitAddCircle) :=
  {f | Function.Bijective f ∧ (∃ F : ℝ → ℝ, Continuous F ∧ StrictAnti F ∧ ∀ x : ℝ, f x = F x) ∧
    ∀ k, f (P.pt k) = Q.pt (c - k)}

/-- **Uniqueness of gluing on the circle (pages 55–58).** The orientation-reversing
homeomorphisms of `AddCircle 1` between two circles with `r` marked points realising a given
anti-isomorphism of `ℤ/r`-torsors form a non-empty contractible space. -/
theorem contractibleSpace_circleGluings (P Q : Marking r) (c : ℤ) :
    ContractibleSpace (circleGluings P Q c) := by
  sorry

end Grothendieck.Folder148

end

-- From Challenge/Folder148Chart.lean
@[expose] public section

namespace Grothendieck.Folder148Chart

/-- The nine types of page 30, by level: the order of `G` for each. `I₁₀` has `G = 𝔻₅` (order 10),
`I₆` has `𝔖₃`, `I₄` has `ℤ/4`; the others have `ℤ/2` or `1`. -/
def orders : List ℕ := [10, 6, 4, 2, 2, 1, 2, 1, 2]

/-- The number of structures of each type, `120 / |G|`. -/
def counts : List ℕ := orders.map (120 / ·)

/-- Level by level, 62, 240 and 240 structures; 542 vertices in all. -/
theorem vertices :
    (counts.take 3).sum = 62 ∧ ((counts.drop 3).take 3).sum = 240 ∧ (counts.drop 6).sum = 240 ∧
      counts.sum = 542 := by
  sorry

end Grothendieck.Folder148Chart

end

-- From Challenge/Folder150.lean
@[expose] public section

open Set

namespace Grothendieck.Folder150

/-- The space `X = [0, 1]`. -/
def X : Set ℝ := Icc 0 1

/-- The closed part `Y = {0}`. -/
def Y : Set ℝ := {0}

/-- The conic neighbourhood `T = [0, 1/2]` of `Y`, for the action `(λ, t) ↦ λ t`. -/
def T : Set ℝ := Icc 0 (1 / 2)

/-- Its boundary `Ṫ = {1/2}`. -/
def Tdot : Set ℝ := {1 / 2}

/-- `X* = X ∖ T° = [1/2, 1]`. -/
def Xstar : Set ℝ := Icc (1 / 2) 1

/-- The cone `I · S = {λ s | λ ∈ [0, 1], s ∈ S}`. -/
def cone (S : Set ℝ) : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Icc 0 1 ×ˢ S)

/-- `C ⊂ T` is conic: `C = I · (C ∩ Ṫ) ∪ (C ∩ Y)` (page 15). -/
def IsConic (C : Set ℝ) : Prop := C ⊆ T ∧ C = cone (C ∩ Tdot) ∪ (C ∩ Y)

/-- `T` is compatible with the closed part `X₁ ⊂ X`: `X₁ ∩ T` is conic. -/
def IsCompatible (X₁ : Set ℝ) : Prop := IsClosed X₁ ∧ X₁ ⊆ X ∧ IsConic (X₁ ∩ T)

/-- `X₁` is compatible with the collar `E = [1/2, 3/4] ≃ Ṫ × [0, 1]`: `X₁ ∩ E = X₁₀ × [0, 1]`
with `X₁₀ = X₁ ∩ Ṫ`. -/
def IsCollarCompatible (X₁ : Set ℝ) : Prop :=
  X₁ ∩ Icc (1 / 2) (3 / 4) = (fun p : ℝ × ℝ => p.1 + p.2 / 4) '' ((X₁ ∩ Tdot) ×ˢ Icc 0 1)

/-- The edition's counterexample (reading, footnote to page 19): `X₁ = {0}` and `X₁ = ∅` are
both compatible with `T` and with the collar, and have the same trace on `X*` — the same
right-hand data `(X*, Ṫ, X₁*, Y, f)` — but `{0}` is nonempty and `∅` is not, so no
isomorphism of systems takes one to the other. -/
theorem compatible_not_determined :
    IsCompatible {0} ∧ IsCompatible ∅ ∧ IsCollarCompatible {0} ∧ IsCollarCompatible ∅ ∧
      ({0} : Set ℝ) ∩ Xstar = ∅ ∩ Xstar ∧ ({0} : Set ℝ).Nonempty := by
  sorry

end Grothendieck.Folder150

end

-- From Challenge/Folder151.lean
@[expose] public section

open Set Topology

namespace Grothendieck.Folder151

/-- The plane `X = X₂`. -/
abbrev P := ℝ × ℝ

/-- The closed stratum `X₁`, the horizontal axis. -/
def axis : Set P := {p | p.2 = 0}

/-- The closed stratum `X₀ = X₀* = {0}`. -/
def X0 : Set P := {0}

/-- The open stratum `X₁* = X₁ ∖ X₀`. -/
def X1s : Set P := axis \ X0

/-- The open stratum `X₂* = X₂ ∖ X₁`. -/
def X2s : Set P := axisᶜ

/-- Arbitrary choices of the closed tubes `𝒱̄_{0,1}` (of `X₀` in `X₁`) and `𝒱̄_{1,2}`
(of `X₁` in `X₂`), each containing its soul. -/
structure Tubes where
  V01bar : Set P
  V12bar : Set P
  V01bar_subset : V01bar ⊆ axis
  X0_subset : X0 ⊆ V01bar
  axis_subset : axis ⊆ V12bar

namespace Tubes

variable (T : Tubes)

/-- `𝒱_{0,1} = 𝒱̄_{0,1} ∖ R_{0,1}`, with `R_{0,1} = ∅`. -/
def V01 : Set P := T.V01bar \ ∅

/-- `𝒱*_{0,1} = 𝒱̄_{0,1} ∖ Ẋ₁`, with `Ẋ₁ = X₀`. -/
def V01s : Set P := T.V01bar \ X0

/-- `𝒱_{1,2} = 𝒱̄_{1,2} ∖ R_{1,2}`, with `R_{1,2} = X₀`. -/
def V12 : Set P := T.V12bar \ X0

/-- `𝒱*_{1,2} = 𝒱̄_{1,2} ∖ Ẋ₂`, with `Ẋ₂ = X₁`. -/
def V12s : Set P := T.V12bar \ axis

/-- The seven vertices of `Ĩ`: `X₀*, 𝒱_{0,1}, 𝒱*_{0,1}, X₁*, 𝒱_{1,2}, 𝒱*_{1,2}, X₂*`. -/
def piece : Fin 7 → Set P := ![X0, T.V01, T.V01s, X1s, T.V12, T.V12s, X2s]

/-- The colimit topology: the finest making the inclusions of the seven vertices continuous. -/
@[instance_reducible]
def colimTop : TopologicalSpace P :=
  ⨆ i, TopologicalSpace.coinduced (Subtype.val : T.piece i → P) inferInstance

/-- The colimit topology of `Ĩ` is not the topology of `ℝ²`: the gluing theorem of page 68,
read as a colimit in `Top`, fails for `ℝ² ⊃ ℝ × {0} ⊃ {0}`, whatever the tubes. -/
theorem colimTop_ne : T.colimTop ≠ (inferInstance : TopologicalSpace P) := by
  sorry

end Tubes

end Grothendieck.Folder151

end

-- From Challenge/Folder152.lean
@[expose] public section

namespace Grothendieck.Folder152

open Equiv

variable {D : Type*}

/-- A fixed-point-free involution of `D`. -/
structure InvolutionSansPointFixe (D : Type*) where
  /-- The involution. -/
  σ : Perm D
  invol : ∀ a, σ (σ a) = a
  sansPointFixe : ∀ a, σ a ≠ a

theorem InvolutionSansPointFixe.mul_self (s : InvolutionSansPointFixe D) :
    s.σ * s.σ = 1 :=
  Equiv.ext s.invol

/-- A combinatorial circularised graph without isolated vertex, on the set of
arcs `D = Ā`: the reversal `σ_Γ` and the rotation `ρ_Γ` (next arc around the
origin). Its vertices are the orbits of `ρ_Γ`. -/
structure GrapheCircularise (D : Type*) where
  /-- The reversal of arcs `σ_Γ`. -/
  σ : InvolutionSansPointFixe D
  /-- The rotation `ρ_Γ`. -/
  ρ : Perm D

/-- An oriented contour `(A(C), ρ_C)` with a fixed-point-free gluing involution
`σ_C`; its polygons (faces) are the cycles of `ρ_C`. -/
structure Contour (D : Type*) where
  /-- "Next edge" on the oriented contour, `ρ_C`. -/
  ρC : Perm D
  /-- The gluing involution `σ_C`. -/
  σC : InvolutionSansPointFixe D

/-- From the graph to its contour: `σ_C = σ_Γ`, `ρ_C = ρ_Γ σ_Γ`. -/
def GrapheCircularise.contour (Γ : GrapheCircularise D) : Contour D :=
  ⟨Γ.ρ * Γ.σ.σ, Γ.σ⟩

/-- From the contour back to the graph: `σ_Γ = σ_C`, `ρ_Γ = ρ_C σ_C`. -/
def Contour.graphe (C : Contour D) : GrapheCircularise D :=
  ⟨C.σC, C.ρC * C.σC.σ⟩

/-- **Équivalence** (on objects). Circularised graphs without isolated vertex
on `Ā` and contours with a fixed-point-free involution on the same set
correspond, by `σ_C = σ_Γ`, `ρ_C = ρ_Γ σ_Γ` and `ρ_Γ = ρ_C σ_C`. -/
def dictionnaire : GrapheCircularise D ≃ Contour D where
  toFun := GrapheCircularise.contour
  invFun := Contour.graphe
  left_inv Γ := by
    obtain ⟨σ, ρ⟩ := Γ
    simp only [GrapheCircularise.contour, Contour.graphe, mul_assoc, σ.mul_self, mul_one]
  right_inv C := by
    obtain ⟨ρC, σ⟩ := C
    simp only [GrapheCircularise.contour, Contour.graphe, mul_assoc, σ.mul_self, mul_one]

/-- The three formulas of the dictionary, all at once: `σ_C = σ_Γ`,
`ρ_C = ρ_Γ σ_Γ`, `ρ_Γ = ρ_C σ_C`. -/
theorem formules (Γ : GrapheCircularise D) :
    (dictionnaire Γ).σC = Γ.σ ∧ (dictionnaire Γ).ρC = Γ.ρ * Γ.σ.σ ∧
      Γ.ρ = (dictionnaire Γ).ρC * (dictionnaire Γ).σC.σ := by
  sorry

end Grothendieck.Folder152

end

-- From Challenge/Folder153.lean
@[expose] public section

namespace Grothendieck.Folder153

open Polynomial TensorProduct

variable {k₀ K₀ : Type*} [CommRing k₀] [CommRing K₀] [Algebra k₀ K₀]

/-- Evaluation at `x ∈ k₀`, as a `k₀`-linear map `K₀[T] → K₀`. -/
noncomputable def ev (x : k₀) : K₀[X] →ₗ[k₀] K₀ :=
  (Polynomial.leval (algebraMap k₀ K₀ x)).restrictScalars k₀

variable (k₀ K₀) in
/-- `Ω = Int(k₀)`: the polynomials of `K₀[T]` taking values in `k₀` on `k₀`. -/
noncomputable def Omega : Subalgebra k₀ K₀[X] where
  carrier := {F | ∀ x : k₀, F.eval (algebraMap k₀ K₀ x) ∈ (algebraMap k₀ K₀).range}
  mul_mem' {F G} hF hG x := by rw [eval_mul]; exact mul_mem (hF x) (hG x)
  add_mem' {F G} hF hG x := by rw [eval_add]; exact add_mem (hF x) (hG x)
  algebraMap_mem' c x := by
    rw [Polynomial.algebraMap_apply, eval_C]; exact ⟨c, rfl⟩

variable {M : Type*} [AddCommGroup M] [Module k₀ M]

variable (K₀ M) in
/-- The set of the Lemme: the `F ∈ K₀[T] ⊗ M` such that `F(x) ∈ M` for every
`x ∈ k₀`, i.e. `(ev_x ⊗ id) F` lies in the image of `m ↦ 1 ⊗ m`. -/
def valeursDansM : Set (K₀[X] ⊗[k₀] M) :=
  {F | ∀ x : k₀, (ev x).rTensor M F ∈ LinearMap.range (TensorProduct.mk k₀ K₀ M 1)}

/-- **Lemme (2).** For `M` free, the image of `Ω ⊗ M → K₀[T] ⊗ M` is exactly the
set of `F` with `F(x) ∈ M` for every `x ∈ k₀`. -/
theorem lemme_range [Module.Free k₀ M] :
    (LinearMap.range ((Omega k₀ K₀).val.toLinearMap.rTensor M) : Set (K₀[X] ⊗[k₀] M)) =
      valeursDansM K₀ M := by
  sorry

end Grothendieck.Folder153

end

-- From Challenge/Folder154.lean
@[expose] public section

namespace Grothendieck.Folder154

/-- The signs read along a line are valid: not all zero, and of the form `a … a (x) −a … −a`
with `a = ±1`, the middle `x` (at position `c`) being `a`, `0` or `−a`: that is
`+ … + (0) − … −` up to reversal, with at most one zero. -/
def ValidSeq {n : ℕ} (s : Fin n → SignType) : Prop :=
  (∃ i, s i ≠ 0) ∧ ∃ a : SignType, a ≠ 0 ∧ ∃ c : ℕ,
    (∀ i : Fin n, (i : ℕ) < c → s i = a) ∧ (∀ i : Fin n, c < (i : ℕ) → s i = -a)

/-- The combinatorial data of an arrangement `Σ`: vertices `V` (one representative cocircuit
for each antipodal pair), lines `L`; line `ℓ` carries the vertices `vert ℓ 0, …` in the order
of its double cover from a base point, `ori ℓ i = ±1` comparing the representative of
`vert ℓ i` with the orientation of `ℓ`. -/
structure Arrangement (V : Type*) (L : Type*) where
  /-- The number of vertices on a line. -/
  len : L → ℕ
  /-- The vertices of a line, in order. -/
  vert : (ℓ : L) → Fin (len ℓ) → V
  vert_injective : ∀ ℓ, Function.Injective (vert ℓ)
  /-- The sign correcting the chosen representative of each vertex along the line. -/
  ori : (ℓ : L) → Fin (len ℓ) → SignType
  ori_ne_zero : ∀ ℓ i, ori ℓ i ≠ 0

/-- `σ` is a specialisation of `τ` (`τ` a generisation of `σ`): `τ = σ` wherever `σ ≠ 0`. -/
def Spec {X : Type*} (σ τ : X → SignType) : Prop := ∀ x, σ x ≠ 0 → τ x = σ x

namespace Arrangement

variable {V L : Type*} (A : Arrangement V L)

/-- The signs of a signature read along the line `ℓ`. -/
def restr (σ : V → SignType) (ℓ : L) : Fin (A.len ℓ) → SignType :=
  fun i => A.ori ℓ i * σ (A.vert ℓ i)

/-- A position of an added pseudoline: a cocircuit signature valid on every line of `Σ`
(Las Vergnas's criterion, with the edition's exclusion of the lines of `Σ` themselves). -/
def IsPosition (σ : V → SignType) : Prop := ∀ ℓ, ValidSeq (A.restr σ ℓ)

variable {A}

/-- The generisations of the position `σ_D`. -/
abbrev Gen (A : Arrangement V L) (σD : V → SignType) :=
  {σ : V → SignType // A.IsPosition σ ∧ Spec σD σ}

end Arrangement

namespace Arrangement

variable {V L : Type*} [Fintype V] {A : Arrangement V L} {σD : V → SignType}

/-- The generisations of `D`: `3^ν`, one for each face of the `ν`-cube, `ν` the number of
vertices through which `D` passes. -/
theorem card_gen (hD : A.IsPosition σD) :
    Nat.card (A.Gen σD) = 3 ^ Fintype.card {v // σD v = 0} := by
  sorry

end Arrangement

end Grothendieck.Folder154

end

-- From Challenge/Folder155.lean
@[expose] public section

namespace Grothendieck.Folder155

open TensorProduct

section Idealiser

variable {S : Type*} [Ring S]

/-- The idealiser `{λ | λL ⊆ L}` of an additive subgroup `L`. -/
def idealiser (L : AddSubgroup S) : Subring S where
  carrier := {a | ∀ l ∈ L, a * l ∈ L}
  mul_mem' {a b} ha hb l hl := by rw [mul_assoc]; exact ha _ (hb l hl)
  one_mem' l hl := by rwa [one_mul]
  add_mem' {a b} ha hb l hl := by rw [add_mul]; exact L.add_mem (ha l hl) (hb l hl)
  zero_mem' l _ := by rw [zero_mul]; exact L.zero_mem
  neg_mem' {a} ha l hl := by rw [neg_mul]; exact L.neg_mem (ha l hl)

end Idealiser

section Takeuchi

variable {k K A : Type*} [CommRing k] [CommRing K] [Algebra k K] [Ring A] [Algebra k A]
  (ι : K →ₐ[k] A)

/-- The generator `ι x ⊗ 1 − 1 ⊗ ι x`. -/
def g (x : K) : A ⊗[k] A := ι x ⊗ₜ 1 - 1 ⊗ₜ ι x

/-- `𝒥`, the right ideal generated by the `ι x ⊗ 1 − 1 ⊗ ι x`. -/
def bigJ : AddSubgroup (A ⊗[k] A) :=
  AddSubgroup.closure {t | ∃ x s, t = g ι x * s}

variable [Module K A] (hι : ∀ (x : K) (a : A), x • a = ι x * a)

include hι

theorem smul_eq_algebraMap (c : k) (a : A) : c • a = algebraMap k K c • a := by
  rw [hι, AlgHom.commutes, Algebra.smul_def]

omit hι in
/-- `(a, b) ↦ a ⊗ b ∈ A ⊗_K A`, biadditive. -/
def tmulK : A →+ A →+ A ⊗[K] A where
  toFun a :=
    { toFun := fun b => a ⊗ₜ[K] b
      map_zero' := tmul_zero _ _
      map_add' := tmul_add a }
  map_zero' := by ext b; exact zero_tmul _ _
  map_add' a a' := by ext b; exact add_tmul _ _ _

/-- The quotient map `A ⊗_k A → A ⊗_K A`. -/
noncomputable def φ : A ⊗[k] A →+ A ⊗[K] A :=
  liftAddHom tmulK fun c a b => by
    change (c • a) ⊗ₜ[K] b = a ⊗ₜ[K] (c • b)
    rw [smul_eq_algebraMap ι hι, smul_eq_algebraMap ι hι, smul_tmul]

@[simp] theorem φ_tmul (a b : A) : φ ι hι (a ⊗ₜ b) = a ⊗ₜ[K] b := rfl

/-- Right multiplication by `ι x` on `A`, a `K`-linear map. -/
def mulRight (x : K) : A →ₗ[K] A where
  toFun a := a * ι x
  map_add' a b := add_mul a b (ι x)
  map_smul' y a := by simp only [hι, RingHom.id_apply, mul_assoc]

/-- `Σ aᵢ ⊗ bᵢ ↦ Σ aᵢ ι(x) ⊗ bᵢ` on `A ⊗_K A`. -/
noncomputable def ρ₁ (x : K) : A ⊗[K] A →ₗ[K] A ⊗[K] A :=
  TensorProduct.map (mulRight ι hι x) LinearMap.id

/-- `Σ aᵢ ⊗ bᵢ ↦ Σ aᵢ ⊗ bᵢ ι(x)` on `A ⊗_K A`. -/
noncomputable def ρ₂ (x : K) : A ⊗[K] A →ₗ[K] A ⊗[K] A :=
  TensorProduct.map LinearMap.id (mulRight ι hι x)

/-- Takeuchi's `A ×_K A`: the `t` with `Σ aᵢ ι(x) ⊗ bᵢ = Σ aᵢ ⊗ bᵢ ι(x)`. -/
def takeuchi : Set (A ⊗[K] A) := {t | ∀ x, ρ₁ ι hι x t = ρ₂ ι hι x t}

/-- **Page 1, the idealiser is Takeuchi's subring**: `λ ∈ 𝒥̃` iff its image in
`A ⊗_K A` lies in `A ×_K A`. -/
theorem mem_idealiser_iff_takeuchi (a : A ⊗[k] A) :
    a ∈ idealiser (bigJ ι) ↔ φ ι hι a ∈ takeuchi ι hι := by
  sorry

end Takeuchi

end Grothendieck.Folder155

end

-- From Challenge/Folder156_1.lean
@[expose] public section

namespace Grothendieck.Folder156_1

open Set

/-- The data of a model of a one-dimensional form (page 5): for each segment
its set of lieux `car I = Ĩ` and its extremities `bd I = ∂I`. -/
structure Data (L S : Type*) where
  /-- the lieux on a segment, `Ĩ` -/
  car : S → Set L
  /-- the extremities of a segment, `∂I` -/
  bd : S → Set L

namespace Data

variable {L S : Type*} (M : Data L S)

/-- The interior lieux `I° = Ĩ ∖ ∂I`. -/
def intr (I : S) : Set L := M.car I \ M.bd I

/-- `J` is the sub-segment `I_{x,z}` of `I`: `J̃ ⊆ Ĩ` and `∂J = {x, z}` (F1). -/
def IsSub (I : S) (x z : L) (J : S) : Prop := M.car J ⊆ M.car I ∧ M.bd J = {x, z}

/-- A regular lieu is interior to some segment (page 7). -/
def Regular (x : L) : Prop := ∃ I, x ∈ M.intr I

/-- `I R_x J`: the segments `I, J` issued from `x` define the same branch at `x`
(page 6): some `z ∈ I° ∩ J°` has `I_{x,z} = J_{x,z}`. -/
def SameBranch (x : L) (I J : S) : Prop :=
  x ∈ M.bd I ∧ x ∈ M.bd J ∧ ∃ z ∈ M.intr I ∩ M.intr J, ∃ K, M.IsSub I x z K ∧ M.IsSub J x z K

/-- The lieu `x` has order two: two segments issued from `x` in different
branches, and every segment issued from `x` in the branch of one of them. -/
def OrderTwo (x : L) : Prop :=
  ∃ I J, x ∈ M.bd I ∧ x ∈ M.bd J ∧ ¬ M.SameBranch x I J ∧
    ∀ K, x ∈ M.bd K → M.SameBranch x K I ∨ M.SameBranch x K J

/-- The axioms F1–F5 and F′3 of the third draft (pages 5–8), as the reading
states them. -/
structure Axioms : Prop where
  /-- `∂I` is a two-element set. -/
  bd_pair : ∀ I, ∃ x y, x ≠ y ∧ M.bd I = {x, y}
  /-- `∂I ⊆ Ĩ`. -/
  bd_sub : ∀ I, M.bd I ⊆ M.car I
  /-- **F1**: for `x ∈ ∂I` and `z ∈ Ĩ ∖ {x}`, there is a unique `I_{x,z}`. -/
  F1 : ∀ I x, x ∈ M.bd I → ∀ z ∈ M.car I, z ≠ x → ∃! J, M.IsSub I x z J
  /-- **F2**, first clause: `I° ≠ ∅`. -/
  F2_intr : ∀ I, (M.intr I).Nonempty
  /-- **F2**: for `∂I = {x, y}` and `z ∈ I°`, `Ĩ_{x,z} ∩ Ĩ_{y,z} = {z}`, and every
  sub-segment of `I` with extremity `z` lies in `I_{x,z}` or in `I_{y,z}`. -/
  F2 : ∀ I x y z, M.bd I = {x, y} → z ∈ M.intr I → ∀ Jx Jy, M.IsSub I x z Jx →
    M.IsSub I y z Jy → M.car Jx ∩ M.car Jy = {z} ∧
      ∀ J, M.car J ⊆ M.car I → z ∈ M.bd J → M.car J ⊆ M.car Jx ∨ M.car J ⊆ M.car Jy
  /-- **F3** (branches), in the margin's form `u ∈ I ∖ {x}`, `v ∈ J ∖ {x}`. -/
  F3 : ∀ I J x, x ∈ M.bd I → x ∈ M.bd J → ∃ u ∈ M.car I, u ≠ x ∧ ∃ v ∈ M.car J, v ≠ x ∧
    ∃ Iu Jv, M.IsSub I x u Iu ∧ M.IsSub J x v Jv ∧ (Iu = Jv ∨ M.car Iu ∩ M.car Jv = {x})
  /-- **F′3** (filtering at an extremity), the reading's reconstruction. -/
  F3' : ∀ I x, x ∈ M.bd I → ∀ u ∈ M.intr I, ∀ v ∈ M.intr I, ∃ w ∈ M.intr I,
    ∀ Iu Iv Iw, M.IsSub I x u Iu → M.IsSub I x v Iv → M.IsSub I x w Iw →
      M.car Iw ⊆ M.car Iu ∩ M.car Iv
  /-- **F4** (gluing at a regular lieu). -/
  F4 : ∀ I' I'' x y z, M.Regular z → M.car I' ∩ M.car I'' = {z} → M.bd I' = {x, z} →
    M.bd I'' = {y, z} → ∃! I, M.car I' ∪ M.car I'' ⊆ M.car I ∧ M.bd I = {x, y}
  /-- **F5**: a regular lieu has order two. -/
  F5 : ∀ x, M.Regular x → M.OrderTwo x

/-- The relation of page 11 from the extremity `x₀`: `a ≤ b` iff `a ∈ [x₀, b]`,
where `[x₀, x₀] = {x₀}` and `[x₀, b] = Ĩ_{x₀,b}` otherwise. -/
def le (x0 : L) (a b : L) : Prop := a = b ∨ ∃ J, M.bd J = {x0, b} ∧ a ∈ M.car J

/-- A model which is a single segment `I = L` (page 10), with `∂I = {x₀, x₁}`. -/
structure SegModel (I : S) (x0 x1 : L) : Prop where
  ax : M.Axioms
  car_eq : M.car I = univ
  bd_eq : M.bd I = {x0, x1}

variable {M}

theorem le_refl' (x0 a : L) : M.le x0 a a := Or.inl rfl

namespace Axioms

variable (hM : M.Axioms)

include hM

theorem ne_of_bd {J : S} {a b : L} (h : M.bd J = {a, b}) : a ≠ b := by
  rintro rfl
  obtain ⟨x, y, hxy, hJ⟩ := hM.bd_pair J
  rcases pair_eq_pair_iff.1 (hJ.symm.trans h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hxy rfl

theorem left_mem {J : S} {a b : L} (h : M.bd J = {a, b}) : a ∈ M.car J :=
  hM.bd_sub J (by rw [h]; simp)

theorem right_mem {J : S} {a b : L} (h : M.bd J = {a, b}) : b ∈ M.car J :=
  hM.bd_sub J (by rw [h]; simp)

/-- The uniqueness clause of F1. -/
theorem sub_unique {P J J' : S} {x z : L} (hx : x ∈ M.bd P) (hz : z ∈ M.car P) (hzx : z ≠ x)
    (hJ : M.IsSub P x z J) (hJ' : M.IsSub P x z J') : J = J' :=
  (hM.F1 P x hx z hz hzx).unique hJ hJ'

end Axioms

namespace SegModel

variable {I : S} {x0 x1 : L} (h : M.SegModel I x0 x1)

include h

theorem x0_bd : x0 ∈ M.bd I := by rw [h.bd_eq]; simp

theorem mem_car (a : L) : a ∈ M.car I := h.car_eq ▸ mem_univ a

theorem isSub {J : S} {e w : L} (hJ : M.bd J = {e, w}) : M.IsSub I e w J :=
  ⟨h.car_eq ▸ subset_univ _, hJ⟩

theorem uniq0 {J J' : S} {b : L} (hJ : M.bd J = {x0, b}) (hJ' : M.bd J' = {x0, b}) :
    J = J' :=
  h.ax.sub_unique h.x0_bd (h.mem_car b) (h.ax.ne_of_bd hJ).symm (h.isSub hJ) (h.isSub hJ')

/-- `[x₀, b] ⊆ [x₀, c]` as soon as `b ∈ [x₀, c]`. -/
theorem car_sub {Jb Jc : S} {b c : L} (hb : M.bd Jb = {x0, b}) (hc : M.bd Jc = {x0, c})
    (hbc : b ∈ M.car Jc) : M.car Jb ⊆ M.car Jc := by
  obtain ⟨K, hK, -⟩ := h.ax.F1 Jc x0 (by rw [hc]; simp) b hbc (h.ax.ne_of_bd hb).symm
  rw [h.uniq0 hb hK.2]; exact hK.1

theorem le_trans' {a b c : L} (hab : M.le x0 a b) (hbc : M.le x0 b c) : M.le x0 a c := by
  rcases hab with rfl | ⟨Jb, hb, ha⟩
  · exact hbc
  rcases hbc with rfl | ⟨Jc, hc, hb'⟩
  · exact Or.inr ⟨Jb, hb, ha⟩
  exact Or.inr ⟨Jc, hc, h.car_sub hb hc hb' ha⟩

theorem le_antisymm' {a b : L} (hab : M.le x0 a b) (hba : M.le x0 b a) : a = b := by
  by_contra hne
  rcases hab with rfl | ⟨Jb, hb, ha⟩
  · exact hne rfl
  rcases hba with hba | ⟨Ja, hJa, hb'⟩
  · exact hne hba.symm
  have ha0 : a ≠ x0 := fun e => by rw [e] at hJa; exact h.ax.ne_of_bd hJa rfl
  have hJab : M.car Ja ⊆ M.car Jb := h.car_sub hJa hb ha
  have hJba : M.car Jb ⊆ M.car Ja := h.car_sub hb hJa hb'
  obtain ⟨K, hK, -⟩ := h.ax.F1 Jb b (by rw [hb]; simp) a ha hne
  have haint : a ∈ M.intr Jb := ⟨ha, by rw [hb]; simp [ha0, hne]⟩
  have h2 := (h.ax.F2 Jb x0 b a hb haint Ja K ⟨hJab, hJa⟩ hK).1
  exact hne (h2.subset ⟨hJba (h.ax.right_mem hb), h.ax.left_mem hK.2⟩).symm

/-- The order of page 11 on the lieux of the segment model. -/
abbrev toPartialOrder : PartialOrder L where
  le := M.le x0
  le_refl := le_refl' x0
  le_trans := fun _ _ _ => h.le_trans'
  le_antisymm := fun _ _ => h.le_antisymm'

end SegModel

end Data

/-- Locally directed downwards (« localement filtrant décroissant », page 12). -/
def LocDirDown (α : Type*) [Preorder α] : Prop :=
  ∀ x y₁ y₂ : α, x < y₁ → x < y₂ → ∃ y, x < y ∧ y ≤ y₁ ∧ y ≤ y₂

/-- Locally directed upwards (« localement filtrant croissant », page 12). -/
def LocDirUp (α : Type*) [Preorder α] : Prop :=
  ∀ x y₁ y₂ : α, y₁ < x → y₂ < x → ∃ y, y₁ ≤ y ∧ y₂ ≤ y ∧ y < x

namespace Data.SegModel

variable {L S : Type*} {M : Data L S} {I : S} {x0 x1 : L} (h : M.SegModel I x0 x1)

include h

/-- **Pages 10–13, forward direction.** In a model which is a single segment
`I = L` with `∂I = {x₀, x₁}`, the order of page 11 has least element `x₀` and
greatest element `x₁`, distinct; it is dense and locally directed downwards and
upwards; every segment is an interval `[a, b]`, `a < b`, with `∂ = {a, b}`, and
every such interval is carried by exactly one segment. Only F1, F2, F′3 and F4
are used. -/
theorem biorder :
    letI := h.toPartialOrder
    (∀ a, x0 ≤ a) ∧ (∀ a, a ≤ x1) ∧ x0 ≠ x1 ∧ DenselyOrdered L ∧ LocDirDown L ∧
      LocDirUp L ∧ (∀ J, ∃ a b, a < b ∧ M.car J = Icc a b ∧ M.bd J = {a, b}) ∧
      (∀ a b : L, a < b → ∃! J, M.car J = Icc a b ∧ M.bd J = {a, b}) := by
  sorry

end Data.SegModel

end Grothendieck.Folder156_1

end

-- From Challenge/Folder156_2.lean
@[expose] public section

namespace Grothendieck.Folder156_2

open Filter Topology

section Ultra

variable {Y : Type*}

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  exacts [Or.inl rfl, Or.inr rfl]

end Ultra

variable {X : Type*} [TopologicalSpace X] (A : Set X)

/-- `f : X → 𝔽₂` is locally constant on `S` (for the subspace topology): it is the indicator
of a part of `S` open and closed in `S`. -/
def LocConst (f : X → ZMod 2) (S : Set X) : Prop := ∀ y ∈ S, ∀ᶠ z in 𝓝[S] y, f z = f y

variable {A}

theorem LocConst.mono {f : X → ZMod 2} {S T : Set X} (h : LocConst f S) (hT : T ⊆ S) :
    LocConst f T := fun y hy => nhdsWithin_mono y hT (h y (hT hy))

theorem LocConst.const (c : ZMod 2) (S : Set X) : LocConst (fun _ => c) S :=
  fun _ _ => Eventually.of_forall fun _ => rfl

theorem LocConst.add {f g : X → ZMod 2} {S : Set X} (hf : LocConst f S) (hg : LocConst g S) :
    LocConst (f + g) S := fun y hy => (hf y hy).mp ((hg y hy).mono fun z h1 h2 => by
      simp [h1, h2])

theorem LocConst.mul {f g : X → ZMod 2} {S : Set X} (hf : LocConst f S) (hg : LocConst g S) :
    LocConst (f * g) S := fun y hy => (hf y hy).mp ((hg y hy).mono fun z h1 h2 => by
      simp [h1, h2])

theorem LocConst.neg {f : X → ZMod 2} {S : Set X} (hf : LocConst f S) :
    LocConst (-f) S := fun y hy => (hf y hy).mono fun z h => by simp [h]

variable (A)

/-- Germs, for the filter `F ⊓ 𝓟 (X ∖ A)`, of functions locally constant on `V ∖ A` for some
`V ∈ F`: the sections of `j_* 𝔽₂` near `F`. -/
def locSec (F : Filter X) : Subring (Germ (F ⊓ 𝓟 Aᶜ) (ZMod 2)) where
  carrier := {g | ∃ V ∈ F, ∃ f : X → ZMod 2, LocConst f (V ∩ Aᶜ) ∧ (f : Germ _ _) = g}
  mul_mem' := by
    rintro _ _ ⟨V, hV, f, hf, rfl⟩ ⟨W, hW, g, hg, rfl⟩
    exact ⟨V ∩ W, inter_mem hV hW, f * g, (hf.mono (by intro; simp_all)).mul
      (hg.mono (by intro; simp_all)), rfl⟩
  one_mem' := ⟨Set.univ, univ_mem, 1, LocConst.const 1 _, rfl⟩
  add_mem' := by
    rintro _ _ ⟨V, hV, f, hf, rfl⟩ ⟨W, hW, g, hg, rfl⟩
    exact ⟨V ∩ W, inter_mem hV hW, f + g, (hf.mono (by intro; simp_all)).add
      (hg.mono (by intro; simp_all)), rfl⟩
  zero_mem' := ⟨Set.univ, univ_mem, 0, LocConst.const 0 _, rfl⟩
  neg_mem' := by
    rintro _ ⟨V, hV, f, hf, rfl⟩
    exact ⟨V, hV, -f, hf.neg, rfl⟩

theorem mem_locSec {F : Filter X} {g : Germ (F ⊓ 𝓟 Aᶜ) (ZMod 2)} :
    g ∈ locSec A F ↔ ∃ V ∈ F, ∃ f : X → ZMod 2, LocConst f (V ∩ Aᶜ) ∧ (f : Germ _ _) = g :=
  Iff.rfl

/-- The rives of `A`: `Riv(A, X) = lim_{V ⊇ A} Comp(V ∖ A)`, germs along `A` of open and closed
parts of `V ∖ A`, as a Boolean ring. -/
abbrev Riv := locSec A (𝓝ˢ A)

/-- The stalk at `x` of `j_* 𝔽₂`, `j : X ∖ A → X`. -/
abbrev Stalk (x : X) := locSec A (𝓝 x)

/-- The relative Stone spectrum `Ã → A` of `(j_* 𝔽₂)|_A`: over `x ∈ A`, the points of the
spectrum of the stalk. -/
def Spec := Σ x : A, (Stalk A x →+* ZMod 2)

/-- Its topology, generated by the sets `{(y, χ) : y ∈ W, χ(germ of f at y) = 1}`, `W` open and
`f` locally constant on `W ∖ A`. -/
instance : TopologicalSpace (Spec A) := TopologicalSpace.generateFrom
  {S | ∃ W : Set X, IsOpen W ∧ ∃ f : X → ZMod 2, LocConst f (W ∩ Aᶜ) ∧
    S = {p | (p.1 : X) ∈ W ∧ ∃ h, p.2 ⟨(f : Germ _ _), h⟩ = 1}}

variable {A}

theorem tendsto_res {x : X} (hx : x ∈ A) :
    Tendsto id (𝓝 x ⊓ 𝓟 Aᶜ) (𝓝ˢ A ⊓ 𝓟 Aᶜ) :=
  inf_le_inf_right _ (nhds_le_nhdsSet hx)

/-- The germ at `x ∈ A` of a rive. -/
def res {x : X} (hx : x ∈ A) (ρ : Riv A) : Stalk A x :=
  ⟨ρ.1.compTendsto id (tendsto_res hx), by
    obtain ⟨g, hg⟩ := ρ
    obtain ⟨V, hV, f, hf, rfl⟩ := (mem_locSec A).1 hg
    exact ⟨V, nhds_le_nhdsSet hx hV, f, hf, rfl⟩⟩

/-- The set of points `(x, χ)` of `Ã` where the germ of `ρ` at `x` takes the value `1`. -/
def toSpecSet (ρ : Riv A) : Set (Spec A) := {p | p.2 (res p.1.2 ρ) = 1}

theorem toSpecSet_eq_basic (ρ : Riv A) : ∃ W : Set X, IsOpen W ∧ ∃ f : X → ZMod 2,
    LocConst f (W ∩ Aᶜ) ∧ toSpecSet ρ = {p | (p.1 : X) ∈ W ∧ ∃ h, p.2 ⟨(f : Germ _ _), h⟩ = 1} := by
  obtain ⟨g, hg⟩ := ρ
  obtain ⟨V, hV, f, hf, rfl⟩ := (mem_locSec A).1 hg
  obtain ⟨W, hW, hAW, hWV⟩ := mem_nhdsSet_iff_exists.1 hV
  refine ⟨W, hW, f, hf.mono (Set.inter_subset_inter_left _ hWV), ?_⟩
  ext p
  simp only [toSpecSet, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact ⟨hAW p.1.2, (res p.1.2 ⟨_, hg⟩).2, by rw [← h]; rfl⟩
  · rintro ⟨-, _, h⟩
    rw [← h]; rfl

theorem isOpen_toSpecSet (ρ : Riv A) : IsOpen (toSpecSet ρ) := by
  obtain ⟨W, hW, f, hf, h⟩ := toSpecSet_eq_basic ρ
  rw [h]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨W, hW, f, hf, rfl⟩

theorem toSpecSet_compl (ρ : Riv A) : (toSpecSet ρ)ᶜ = toSpecSet (1 - ρ) := by
  ext p
  simp only [toSpecSet, Set.mem_compl_iff, Set.mem_ofPred_eq]
  have : res p.1.2 (1 - ρ) = 1 - res p.1.2 ρ := by
    obtain ⟨g, -⟩ := ρ
    apply Subtype.ext
    induction g using Germ.inductionOn with | h f => rfl
  rw [this, map_sub, map_one]
  rcases zmod2_cases (p.2 (res p.1.2 ρ)) with h | h <;> rw [h] <;> decide

/-- The canonical map `(*)` of page 15, `Riv(A, X) → Comp(Ã)`. -/
def toComp (ρ : Riv A) : TopologicalSpace.Clopens (Spec A) :=
  ⟨toSpecSet ρ, ⟨by rw [← isOpen_compl_iff, toSpecSet_compl]; exact isOpen_toSpecSet _,
    isOpen_toSpecSet ρ⟩⟩

/-- Page 15: the map `(*) : Riv(A, X) → Comp(Ã)` is injective. Neither paracompactness nor the
closedness of `A` is used. -/
theorem toComp_injective : Function.Injective (toComp (A := A)) := by
  sorry

end Grothendieck.Folder156_2

end

-- From Challenge/Folder156_3.lean
@[expose] public section

namespace Grothendieck.Folder156_3

open Set

section Defs

variable {α : Type*} [PartialOrder α]

/-- `x` and `y` are comparable. -/
def Cmp (x y : α) : Prop := x ≤ y ∨ y ≤ x

/-- Strict betweenness `𝓡(a, b, c)`: `a < b < c` or `a > b > c` (page 11). -/
def Btw (a b c : α) : Prop := (a < b ∧ b < c) ∨ (c < b ∧ b < a)

/-- `t ∈ C({a, b})`: `t ∉ {a, b}` and `{a, b, t}` is a chain (page 14). -/
def InC (a b t : α) : Prop := t ≠ a ∧ t ≠ b ∧ Cmp t a ∧ Cmp t b

/-- `s` and `t` lie in the same piece of `C({a, b})`: both below `a` and `b`,
both strictly between them, or both above them (pages 8 and 14). The relation
is symmetric in `a, b`, so it depends only on the pair. -/
def SamePiece (a b s t : α) : Prop :=
  (s < a ∧ s < b ∧ t < a ∧ t < b) ∨ (Btw a s b ∧ Btw a t b) ∨ (a < s ∧ b < s ∧ a < t ∧ b < t)

/-- A tronçon ordonné (page 8). -/
structure Troncon (α : Type*) [PartialOrder α] : Prop where
  /-- a) `L_{>a}` is directed downwards. -/
  dir_down : ∀ a x y : α, a < x → a < y → ∃ z, a < z ∧ z ≤ x ∧ z ≤ y
  /-- a′) `L_{<a}` is directed upwards. -/
  dir_up : ∀ a x y : α, x < a → y < a → ∃ z, x ≤ z ∧ y ≤ z ∧ z < a
  /-- b) `L` is directed downwards … -/
  low : ∀ x y : α, ∃ z, z ≤ x ∧ z ≤ y
  /-- … and upwards. -/
  high : ∀ x y : α, ∃ z, x ≤ z ∧ y ≤ z
  /-- c) `L` is dense (« divisible »). -/
  dense : ∀ x y : α, x < y → ∃ z, x < z ∧ z < y
  /-- d) `card L > 1`. -/
  card : ∃ x y : α, x ≠ y

end Defs

section Transport

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- The data of page 14 preserved by a bijection `e`: comparability, and for each
comparable pair `ε` the partition of `C(ε)` into its pieces. -/
structure PreservesCuts (e : α ≃ β) : Prop where
  cmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y
  piece : ∀ a b, a ≠ b → Cmp a b → ∀ s t, InC a b s → InC a b t →
    (SamePiece (e a) (e b) (e s) (e t) ↔ SamePiece a b s t)

end Transport

section Order

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- **The finding, pages 11–15.** A bijection between tronçons ordonnés that
preserves comparability and, for every comparable pair `ε`, the partition of
`C(ε)` into its pieces, is an order isomorphism or an order anti-isomorphism.
Only conditions b) and c) of page 8 are used. -/
theorem order_of_cuts (hα : Troncon α) (hβ : Troncon β) {e : α ≃ β}
    (he : PreservesCuts e) :
    (∀ x y, e x ≤ e y ↔ x ≤ y) ∨ (∀ x y, e y ≤ e x ↔ x ≤ y) := by
  sorry

end Order

end Grothendieck.Folder156_3

end

-- From Challenge/Folder156_4.lean
@[expose] public section

namespace Grothendieck.Folder156_4

section Hexagon

/-- The minimal multistrates under each `v`. -/
def below : Fin 7 → Finset (Fin 7) :=
  ![{0}, {1}, {2}, {3}, {0, 1, 4}, {1, 2, 5}, {2, 3, 6}]

/-- The order: `x ≤ y` iff `x ∈ 𝓜_{≤y}`. -/
def le (x y : Fin 7) : Prop := x ∈ below y

/-- `R`: generated by the pairs inside each `𝓜_{≤v}`. -/
def rel (x y : Fin 7) : Prop := ∃ v, x ∈ below v ∧ y ∈ below v

instance : DecidableRel le := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

instance : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (∃ _, _))

/-- Disjointness in the model. -/
def disj (x y : Fin 7) : Prop := rel x y ∧ ∀ z, ¬ (le z x ∧ le z y)

instance : DecidableRel disj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The cosupport of a part of the model. -/
def cosuppH (Φ : Finset (Fin 7)) : Finset (Fin 7) := Finset.univ.filter fun x => ∀ y ∈ Φ, disj x y

/-- The support of a part of the model. -/
def suppH (Φ : Finset (Fin 7)) : Finset (Fin 7) := cosuppH (cosuppH Φ)

/-- **The lattice of saturated parts is not distributive**: with meet the intersection and
join the support of the union, `{b, d} ∧ ({b} ∨ {c}) = {b, d}` while
`({b, d} ∧ {b}) ∨ ({b, d} ∧ {c}) = {b}`. -/
theorem hexagon_not_distrib :
    ({1, 3} : Finset (Fin 7)) ∩ suppH ({1} ∪ {2}) = {1, 3} ∧
      suppH (({1, 3} : Finset (Fin 7)) ∩ {1} ∪ {1, 3} ∩ {2}) = {1} := by
  sorry

end Hexagon

end Grothendieck.Folder156_4

end

-- From Challenge/Folder158.lean
@[expose] public section

namespace Grothendieck.Folder158

universe u

/-- **Pseudo-cofiltrant** (the reading's footnote, from manuscript p. 55):
`∀ u, v`, `∃ u', v'` with `u u' = v v'` — any two principal right ideals meet. -/
def PseudoCofiltrant (M : Type u) [Monoid M] : Prop :=
  ∀ u v : M, ∃ u' v' : M, u * u' = v * v'

/-- **Cofiltrant**: pseudo-cofiltrant, and any two parallel arrows (here, any
two elements) are equalised further on: `∀ u, v`, `∃ w` with `u w = v w`. -/
def Cofiltrant (M : Type u) [Monoid M] : Prop :=
  PseudoCofiltrant M ∧ ∀ u v : M, ∃ w : M, u * w = v * w

/-- **Groupe enveloppant trivial**: every monoid morphism from `M` to a group is
trivial (the universal property of the group completion, for groups in `M`'s
universe, where the group completion lives). -/
def GroupeEnveloppantTrivial (M : Type u) [Monoid M] : Prop :=
  ∀ (G : Type u) [Group G] (f : M →* G), f = 1

variable {M : Type u} [Monoid M]

/-- **Proposition 1.** Let `M` be a finite pseudo-cofiltering monoid with
trivial group completion. Then there is `p ∈ M` with `u p = p` for every
`u ∈ M`; in particular `p² = p`, and `M` is cofiltering. -/
theorem proposition1 [Finite M] (hpc : PseudoCofiltrant M)
    (hG : GroupeEnveloppantTrivial M) :
    ∃ p : M, (∀ u : M, u * p = p) ∧ p * p = p ∧ Cofiltrant M := by
  sorry

open CategoryTheory

universe v w

end Grothendieck.Folder158

end

-- From Challenge/Folder160.lean
@[expose] public section

open Matrix Polynomial

namespace Grothendieck.Folder160

variable {R : Type*} [CommRing R] (p : ℕ)

/-- The Moore matrix `(ξ_j^{p^i})`. -/
def mooreMat {n : ℕ} (ξ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => ξ j ^ p ^ (i : ℕ)

/-- The Moore determinant `Δₙ(ξ) = det(ξ_j^{p^i})`. -/
def moore {n : ℕ} (ξ : Fin n → R) : R := (mooreMat p ξ).det

variable [hp : Fact p.Prime]

/-- `D(T) = Δ_{n+1}(T, X₁, …, Xₙ)`, a polynomial in `T` over `𝔽_p[X₁, …, Xₙ]`. -/
noncomputable def D (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  moore p (Fin.cons Polynomial.X fun k => Polynomial.C (MvPolynomial.X k))

/-- `P(T) = ∏_{λ ∈ 𝔽_p^n} (T − λ · X) = D(T)/((−1)ⁿ Δₙ)`. -/
noncomputable def P (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  ((D p n).roots.map fun a => Polynomial.X - Polynomial.C a).prod

/-- The Dickson coefficients `A_i`, polynomials in `X₁, …, Xₙ`. -/
noncomputable def A (n i : ℕ) : MvPolynomial (Fin n) (ZMod p) := (P p n).coeff (p ^ i)

variable {S : Type*} [CommRing S] [Algebra (ZMod p) S]

theorem A_zero_eval {n : ℕ} (ξ : Fin n → S) :
    MvPolynomial.aeval ξ (A p n 0) = (-1) ^ n * moore p ξ ^ (p - 1) := by
  sorry

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

end Grothendieck.Folder160

end

-- From Challenge/Folder161_1.lean
@[expose] public section

namespace Grothendieck.Folder161_1

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {E : Type u₁} [Category.{v₁} E] {F : Type u₂} [Category.{v₂} F]
  {u : E ⥤ F} {v : F ⥤ E} (adj : u ⊣ v)

section Contractions

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- The action of a scalar `e ∈ End(𝟙)` on an object `X`. -/
def scalar (e : 𝟙_ C ⟶ 𝟙_ C) (X : C) : X ⟶ X :=
  (λ_ X).inv ≫ e ▷ X ≫ (λ_ X).hom

/-- If `Y ⊗ X ≅ 𝟙` and `X ⊗ Y ≅ 𝟙`, tensoring on the left with `X` is an
equivalence, with quasi-inverse tensoring with `Y`. -/
def tensorLeftEquivOfInverse {X Y : C} (i : Y ⊗ X ≅ 𝟙_ C) (j : X ⊗ Y ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft X) (tensorLeft Y)
    (NatIso.ofComponents (fun Z => (λ_ Z).symm ≪≫ whiskerRightIso i.symm Z ≪≫ α_ Y X Z)
      (by
        intro _ _ f
        dsimp
        simp only [whiskerRightIso_hom, Iso.symm_hom, Category.assoc]
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
        simp))
    (NatIso.ofComponents (fun Z => (α_ X Y Z).symm ≪≫ whiskerRightIso j Z ≪≫ λ_ Z)
      (by
        intro _ _ f
        dsimp
        simp only [whiskerRightIso_hom, Category.assoc]
        rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
        simp))

variable [SymmetricCategory C] {L L' : C}

open BraidedCategory

/-- `φ_{L',L} = φ_{L,L'} ∘ s_{L',L}`, the trivialisation of `L' ⊗ L` through the
symmetry (page 12). -/
def phiSwap (φ : L ⊗ L' ≅ 𝟙_ C) : L' ⊗ L ≅ 𝟙_ C := β_ L' L ≪≫ φ

/-- Tensoring with an invertible `L` is fully faithful. -/
def fullyFaithfulL (φ : L ⊗ L' ≅ 𝟙_ C) : (tensorLeft L).FullyFaithful :=
  (tensorLeftEquivOfInverse (phiSwap φ) φ).fullyFaithfulFunctor

/-- `ψ_{L',L} : L' ⊗ L ≅ 𝟙`, defined by the triangle identity
`φ_{L,L'} ⊗ id_L = id_L ⊗ ψ_{L',L}` (page 12). -/
def psi (φ : L ⊗ L' ≅ 𝟙_ C) : L' ⊗ L ≅ 𝟙_ C :=
  (fullyFaithfulL φ).preimageIso
    ((α_ L L' L).symm ≪≫ whiskerRightIso φ L ≪≫ λ_ L ≪≫ (ρ_ L).symm)

/-- **Page 12, « Relations entre `φ_{L',L}` et `ψ_{L',L}` ? »** For a scalar `e`,
`φ_{L',L} = e · ψ_{L',L}` if and only if the symmetry acts on `L ⊗ L` by `e`. -/
theorem phiSwap_eq_iff (φ : L ⊗ L' ≅ 𝟙_ C) (e : 𝟙_ C ⟶ 𝟙_ C) :
    (phiSwap φ).hom = (psi φ).hom ≫ e ↔ (β_ L L).hom = scalar e (L ⊗ L) := by
  sorry

end Contractions

end Grothendieck.Folder161_1

end

-- From Challenge/Folder161_2.lean
@[expose] public section

namespace Grothendieck.Folder161_2

open CategoryTheory Limits

section GabrielUlmer

universe w v u

variable (C : Type u) [Category.{v} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]

/-- **Page 61, Corollaire.** « Une `𝒰`-catégorie cocomplète `E` est équivalente à
un `Ind_π(𝒞)`, `𝒞` petite, si et seulement si elle admet une petite
sous-catégorie strictement génératrice formée d'objets accessibles. »

In current terms: a cocomplete, locally small category is locally presentable
iff it has a small full subcategory which is dense (« strictement génératrice »:
every object is the canonical colimit over `𝒞/X`) and made of presentable
(« accessibles ») objects. mathlib's `IsLocallyPresentable` stands for the left
side: cocomplete, with a small family of `κ`-presentable objects of which every
object is a `κ`-filtered colimit — i.e. `E ≃ Ind_κ(𝒞)`. -/
theorem caracterisation_gabriel_ulmer :
    IsLocallyPresentable.{w} C ↔
      ∃ P : ObjectProperty C, ObjectProperty.Small.{w} P ∧ P.ι.IsDense ∧
        ∀ X, P X → IsPresentable.{w} X := by
  sorry

end GabrielUlmer

end Grothendieck.Folder161_2

end

-- From Challenge/Folder161_3.lean
@[expose] public section

namespace Grothendieck.Folder161_3

open TopologicalSpace Set

/-- The page's hypothesis: every nonempty locally closed `Z ⊆ X` has a point `x`
with a quasi-compact neighbourhood `T` in `Z`, i.e. `O ∩ Z ⊆ T ⊆ Z` for an
open `O ∋ x`. -/
def HypG (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Z : Set X, IsLocallyClosed Z → Z.Nonempty →
    ∃ x ∈ Z, ∃ T ⊆ Z, IsCompact T ∧ ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ∩ Z ⊆ T

/-- A set of pairs of opens, stable under shrinking and under arbitrary unions in
each variable: an element of the frame coproduct of `Opens X` and `Opens Y`, the
« S » of the page. -/
@[ext]
structure CIdeal (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] where
  carrier : Set (Opens X × Opens Y)
  mono : ∀ {U U' V V'}, (U, V) ∈ carrier → U' ≤ U → V' ≤ V → (U', V') ∈ carrier
  sSup_left : ∀ (s : Set (Opens X)) V,
    (∀ U ∈ s, (U, V) ∈ carrier) → (sSup s, V) ∈ carrier
  sSup_right : ∀ U (s : Set (Opens Y)),
    (∀ V ∈ s, (U, V) ∈ carrier) → (U, sSup s) ∈ carrier

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pages 10–11: under `HypG X`, a `CIdeal` contains every rectangle covered by
its own rectangles. -/
theorem covering (hG : HypG X) (S : CIdeal X Y) (U : Opens X) (V : Opens Y)
    (h : (U : Set X) ×ˢ (V : Set Y) ⊆ ⋃ p ∈ S.carrier, (p.1 : Set X) ×ˢ (p.2 : Set Y)) :
    (U, V) ∈ S.carrier := by
  sorry

open Function (eval update update_of_ne update_self)

end Grothendieck.Folder161_3

end

