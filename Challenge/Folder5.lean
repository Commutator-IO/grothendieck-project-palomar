module

public import Mathlib

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
