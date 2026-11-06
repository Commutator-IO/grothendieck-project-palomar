module

public import Mathlib

@[expose] public section


/-!
# Folder 5: the coefficients `qᵢ` of the universal divided-power algebra (page 4)

Finding `5-universal-artinian-pd-normal-form` (`src/content/findings.ts`), on the
reading `transcripts/5/5.modern.tex`. Page 4 presents the universal artinian
local `W(k)`-algebra whose maximal ideal carries divided powers killed in degrees
`≥ p^{ν+1}` as `W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛ_{i+1}, Λ_ν^p, Λ₀ − p)`, with
`qᵢ = (p^{i+1})!/((p^i)!)^p`; the relation is `γ_{p^i}(x)^p = qᵢ γ_{p^{i+1}}(x)`.

**Partial.** What is proved is the arithmetic of the `qᵢ`, the « Tier 1 piece »
of issue #54:

* `factorial_eq_mul_q`, `q_eq_multinomial`: `((p^i)!)^p · qᵢ = (p^{i+1})!`, so
  `qᵢ` is an integer, the multinomial coefficient of `p` blocks of size `p^i`;
* `padicValNat_q`: for `p` prime, `v_p(qᵢ) = 1`, by Legendre in the form
  `v_p((pm)!) = v_p(m!) + m` and `(p − 1) v_p((p^i)!) = p^i − 1`
  (`sub_one_mul_padicValNat_factorial_pow`);
* `dpow_pow_eq_q`: in any ring with a divided-power ideal (mathlib's
  `DividedPowers`), `γ_{p^i}(x)^p = qᵢ γ_{p^{i+1}}(x)`, the relation of the
  presentation (a specialisation of mathlib's `DividedPowers.prod_dpow`).

Not formalised: the universality of the presentation, the normal form in the
coordinates `Θᵢ = Λᵢ − p^{p^i}/(p^i)!` (pages 5–7), the constant `c(ν)`, the
quotients `W^{(ν,r)}`, the bound of page 8.
-/

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

/-- Legendre for `p^i`: `(p − 1) v_p((p^i)!) = p^i − 1`. -/
theorem sub_one_mul_padicValNat_factorial_pow (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    (p - 1) * padicValNat p (p ^ i)! = p ^ i - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', padicValNat_factorial_mul, mul_add, ih]
    have h1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.out.pos
    have h2 : (p - 1) * p ^ i + p ^ i = p * p ^ i := by
      rw [Nat.sub_one_mul]
      have := Nat.le_mul_of_pos_left (p ^ i) hp.out.pos
      omega
    omega

/-- **`v_p(qᵢ) = 1`.** -/
theorem padicValNat_q (p : ℕ) [hp : Fact p.Prime] (i : ℕ) : padicValNat p (q p i) = 1 := by
  have hA := sub_one_mul_padicValNat_factorial_pow p i
  have hB : padicValNat p (p ^ (i + 1))! = padicValNat p (p ^ i)! + p ^ i := by
    rw [pow_succ']; exact padicValNat_factorial_mul _
  have hfac := factorial_eq_mul_q p i
  have hq0 : q p i ≠ 0 := by
    intro h; rw [h, mul_zero] at hfac; exact factorial_ne_zero _ hfac
  have hv := congrArg (padicValNat p) hfac
  rw [padicValNat.mul (pow_ne_zero _ (factorial_ne_zero _)) hq0,
    padicValNat.pow] at hv
  have h2 : p * padicValNat p (p ^ i)! =
      (p - 1) * padicValNat p (p ^ i)! + padicValNat p (p ^ i)! := by
    rw [Nat.sub_one_mul]
    have := Nat.le_mul_of_pos_left (padicValNat p (p ^ i)!) hp.out.pos
    omega
  have h1 : 1 ≤ p ^ i := Nat.one_le_pow _ _ hp.out.pos
  omega

/-- `γ_m(x)^p` is the multinomial coefficient times `γ_{pm}(x)`. -/
theorem dpow_pow {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {x : A}
    (hx : x ∈ I) (p m : ℕ) :
    hI.dpow m x ^ p =
      (Nat.multinomial (Finset.range p) (fun _ => m) : A) * hI.dpow (p * m) x := by
  have := hI.prod_dpow (s := Finset.range p) (n := fun _ => m) hx
  simpa [Finset.prod_const, Finset.sum_const] using this

/-- **The relation of page 4**: `γ_{p^i}(x)^p = qᵢ γ_{p^{i+1}}(x)`. -/
theorem dpow_pow_eq_q {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {x : A}
    (hx : x ∈ I) (p i : ℕ) : hI.dpow (p ^ i) x ^ p = (q p i : A) * hI.dpow (p ^ (i + 1)) x := by
  rw [dpow_pow hI hx, q_eq_multinomial, ← pow_succ']

end Grothendieck.Folder5

/-!
## Universality of the presentation (page 4) and the sufficiency half of page 5

Added for issue #89 (finding `5-universal-artinian-pd-normal-form`). Over any domain `W` of
characteristic zero in which the integers prime to `p` are units (`W(k)`, `ℤ_p`; for `ℤ_p` see
`padicInt_isUnit_natCast`):

* `Aν` is `A^{(ν)} = W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p)` and `Wν = A^{(ν)}/(Λ₀ − p)` is the
  page's `W^{(ν)}` (`presentation`: the quotient by all the relations at once);
* `psi_injective`: `Λᵢ ↦ X^{p^i}/(p^i)!` embeds `A^{(ν)}` in `K[X]/(X^{p^{ν+1}})`, `K = Frac W`;
  the box monomials `Λ^a`, `0 ≤ aᵢ < p`, span `A^{(ν)}` (`boxSpan_eq_top`, the carry of page 8)
  and go to nonzero multiples of distinct powers of `X` (`deg_injective`);
* `dpIbar`: hence `(Λ₀, …, Λ_ν)` carries divided powers, those of `x^n/n!` (`psi_hmem`: every
  `γ_k(X)` comes back, by `C(k, p^e) γ_k = γ_{p^e} γ_{k − p^e}` with `C(k, p^e)` prime to `p`,
  `dpow_split`, Lucas);
* `isSubDPIdeal_Kp`, `dpWν`: `(Λ₀ − p) ∩ (Λ) = (Λ₀ − p)(Λ)` is a sub-divided-power ideal, so the
  divided powers pass to `J = (Λ₀, …, Λ_ν) ⊂ W^{(ν)}`, with `γ_{p^i}(p) = Λᵢ` (`dpWν_p`) and
  `γ_n = 0` on `J` for `n ≥ p^{ν+1}` (`dpWν_eq_zero`);
* **`universal`**: `W^{(ν)}` is initial among `W`-algebras with a divided-power ideal `(I, γ)`
  containing `p` with `γ_n(p) = 0` for `n ≥ p^{ν+1}` — locality, artinianity and the residue
  field play no role;
* `p_pow_mul_Θ_mem`, `p_pow_mul_lam_pow_mem`, `p_pow_mem_Kp`: for any `λᵢ ∈ W` with `λ₀ = p`,
  `λᵢ^p = qᵢλᵢ₊₁`, and `Θᵢ = Λᵢ − λᵢ`: `p^iΘᵢ = 0` and `p^ν λ_ν^p = 0` in `W^{(ν)}`, so
  `p^{ν + pm} = 0` when `λ_ν = p^m · unit` (the sufficiency half of the lemma of page 5).

Not formalised: the necessity half of the lemma of page 5 (that conditions a)–b) cut out an
ideal), hence the normal form, the length, the exact order `p^{c(ν)}` of `1`, and the quotients
`W^{(ν,r)}` of page 7.
-/

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

/-- `ofInjective` is compatible with the map. -/
theorem _root_.DividedPowers.ofInjective_dpow_apply {A B : Type*} [CommSemiring A] [CommSemiring B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : Function.Injective f)
    (hJ : DividedPowers J) (hIJ : I.map f = J)
    (hmem : ∀ (n : ℕ) {x : A} (_ : x ∈ I), ∃ (y : A) (_ : n ≠ 0 → y ∈ I), f y = hJ.dpow n (f x))
    {n : ℕ} {x : A} (hx : x ∈ I) :
    f ((DividedPowers.ofInjective I J f hf hJ hIJ hmem).dpow n x) = hJ.dpow n (f x) := by
  simp only [DividedPowers.ofInjective, dite_eq_left hx]
  exact (Exists.choose_spec (hmem n hx)).2

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

private theorem psi_inj_frac : Function.Injective (psi W p ν (FractionRing W)) :=
  psi_injective W p ν _ (IsFractionRing.injective W _) (Fact.out : p.Prime).pos

theorem psi_dpIbar {n : ℕ} {x : Aν W p ν} (hx : x ∈ Ibar W p ν) :
    psi W p ν (FractionRing W) ((dpIbar W p ν hW).dpow n x) =
      (ratDP p ν (FractionRing W) ((Ibar W p ν).map (psi W p ν (FractionRing W)))).dpow n
        (psi W p ν (FractionRing W) x) :=
  DividedPowers.ofInjective_dpow_apply _ _ _ _ _ _ _ hx

/-- `γ_{p^i}(Λ₀) = Λᵢ` in `A^{(ν)}`. -/
theorem dpIbar_Lam_zero (i : Fin (ν + 1)) :
    (dpIbar W p ν hW).dpow (p ^ (i : ℕ)) (Lam W p ν 0) = Lam W p ν i := by
  apply psi_inj_frac
  rw [psi_dpIbar W p ν hW (Lam_mem_Ibar W p ν 0), psi_Lam_zero, psi_Lam_eq_dpow]

omit [IsDomain W] [CharZero W] in
theorem map_Ibar_le (K : Type*) [Field K] [CharZero K] [Algebra W K] :
    (Ibar W p ν).map (psi W p ν K) ≤ Ideal.span {xb p ν K} := by
  rw [Ibar, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [psi_Lam, ← pow_sub_one_mul (a := xb p ν K) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    ← mul_assoc]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- The divided powers of `(Λ)` vanish in degrees `≥ p^{ν+1}`. -/
theorem dpIbar_eq_zero {n : ℕ} (hn : p ^ (ν + 1) ≤ n) {x : Aν W p ν} (hx : x ∈ Ibar W p ν) :
    (dpIbar W p ν hW).dpow n x = 0 := by
  apply psi_inj_frac
  rw [psi_dpIbar W p ν hW hx, map_zero, DividedPowers.RatAlgebra.dpow_apply,
    ite_eq_left (Ideal.mem_map_of_mem _ hx)]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp
    (map_Ibar_le W p ν (FractionRing W) (Ideal.mem_map_of_mem _ hx))
  rw [← ha, mul_pow, xb_pow_eq_zero p ν _ hn, mul_zero, mul_zero]

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

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem mk_Lam_zero : Ideal.Quotient.mk (Kp W p ν) (Lam W p ν 0) = (p : Wν W p ν) := by
  rw [← map_natCast (Ideal.Quotient.mk (Kp W p ν)), Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton_self _

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem p_mem_Jν : (p : Wν W p ν) ∈ (Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν)) := by
  rw [← mk_Lam_zero]; exact Ideal.mem_map_of_mem _ (Lam_mem_Ibar W p ν 0)

/-- **`γ_{p^i}(p) = Λᵢ` in `W^{(ν)}`**: the `Λᵢ` are the divided powers of `p`. -/
theorem dpWν_p (i : Fin (ν + 1)) :
    (dpWν W p ν hW).dpow (p ^ (i : ℕ)) (p : Wν W p ν) =
      Ideal.Quotient.mk (Kp W p ν) (Lam W p ν i) := by
  rw [← mk_Lam_zero, dpWν, DividedPowers.Quotient.dpow_apply _ _ (Lam_mem_Ibar W p ν 0),
    dpIbar_Lam_zero]

/-- **The divided powers of `W^{(ν)}` are `ν`-nilpotent**: `γ_n(y) = 0` on `J` for
`n ≥ p^{ν+1}`. -/
theorem dpWν_eq_zero {n : ℕ} (hn : p ^ (ν + 1) ≤ n) {y : Wν W p ν} (hy : y ∈ (Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν))) :
    (dpWν W p ν hW).dpow n y = 0 := by
  obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
  rw [dpWν, DividedPowers.Quotient.dpow_apply _ _ hx, dpIbar_eq_zero W p ν hW hn hx, map_zero]

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
/-- `W^{(ν)}` is the quotient of `W[Λ₀, …, Λ_ν]` by all the relations of page 4 at once. -/
theorem Kp_eq_map : Kp W p ν = (Ideal.span {X 0 - (p : MvPolynomial (Fin (ν + 1)) W)}).map
    (Ideal.Quotient.mkₐ W (rel W p ν)) := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_natCast, Kp]
  rfl

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
/-- **The presentation of page 4**: `W^{(ν)} ≃ W[Λ₀, …, Λ_ν]/(Λᵢ^p − qᵢΛᵢ₊₁, Λ_ν^p, Λ₀ − p)`. -/
noncomputable def presentation : Wν W p ν ≃ₐ[W] MvPolynomial (Fin (ν + 1)) W ⧸
    (rel W p ν ⊔ Ideal.span {X 0 - (p : MvPolynomial (Fin (ν + 1)) W)}) :=
  (Ideal.quotientEquivAlgOfEq W (Kp_eq_map W p ν)).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ W _ _)

section Lift

variable {T : Type*} [CommRing T] [Algebra W T] {I : Ideal T} (hI : DividedPowers I)
  (hpI : (p : T) ∈ I) (hnil : ∀ n, p ^ (ν + 1) ≤ n → hI.dpow n (p : T) = 0)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
include hpI hnil in
theorem rel_le_ker_lift :
    rel W p ν ≤ RingHom.ker (aeval (R := W) fun i : Fin (ν + 1) => hI.dpow (p ^ (i : ℕ)) (p : T)) := by
  rw [rel, Ideal.span_le]
  rintro _ (⟨i, rfl⟩ | rfl)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast,
      aeval_X, Fin.val_castSucc, Fin.val_succ]
    rw [dpow_pow_eq_q hI hpI, sub_self]
  · simp only [SetLike.mem_coe, RingHom.mem_ker, map_pow, aeval_X, Fin.val_last]
    rw [dpow_pow_eq_q hI hpI, hnil _ le_rfl, mul_zero]

/-- `Λᵢ ↦ γ_{p^i}(p)` on `A^{(ν)}`. -/
noncomputable def lift1 : Aν W p ν →ₐ[W] T :=
  Ideal.Quotient.liftₐ (rel W p ν) (aeval fun i : Fin (ν + 1) => hI.dpow (p ^ (i : ℕ)) (p : T))
    fun _ ha => RingHom.mem_ker.mp (rel_le_ker_lift W p ν hI hpI hnil ha)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem lift1_Lam (i : Fin (ν + 1)) :
    lift1 W p ν hI hpI hnil (Lam W p ν i) = hI.dpow (p ^ (i : ℕ)) (p : T) := by
  change aeval _ (X i) = _
  rw [aeval_X]

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem Kp_le_ker_lift1 : Kp W p ν ≤ RingHom.ker (lift1 W p ν hI hpI hnil) := by
  rw [Kp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
    lift1_Lam, map_natCast, Fin.val_zero, pow_zero, hI.dpow_one hpI, sub_self]

/-- The `W`-algebra map `W^{(ν)} → T`, `Λᵢ ↦ γ_{p^i}(p)`. -/
noncomputable def lift : Wν W p ν →ₐ[W] T :=
  Ideal.Quotient.liftₐ (Kp W p ν) (lift1 W p ν hI hpI hnil)
    fun _ ha => RingHom.mem_ker.mp (Kp_le_ker_lift1 W p ν hI hpI hnil ha)

omit [IsDomain W] [CharZero W] [Fact p.Prime] in
theorem lift_Lam (i : Fin (ν + 1)) :
    lift W p ν hI hpI hnil (Ideal.Quotient.mk _ (Lam W p ν i)) = hI.dpow (p ^ (i : ℕ)) (p : T) :=
  lift1_Lam W p ν hI hpI hnil i

include hW in
theorem lift_dpow_pow (e : ℕ) :
    lift W p ν hI hpI hnil ((dpWν W p ν hW).dpow (p ^ e) (p : Wν W p ν)) =
      hI.dpow (p ^ e) (p : T) := by
  by_cases he : e ≤ ν
  · have := dpWν_p W p ν hW ⟨e, by omega⟩
    simp only at this
    rw [this, lift_Lam]
  · have hle : p ^ (ν + 1) ≤ p ^ e :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    rw [dpWν_eq_zero W p ν hW hle (p_mem_Jν W p ν), map_zero, hnil _ hle]

include hW in
/-- `f(γ_k(p)) = γ_k(p)` for every `k`, by induction on `k` through `dpow_split`. -/
theorem lift_dpow (k : ℕ) :
    lift W p ν hI hpI hnil ((dpWν W p ν hW).dpow k (p : Wν W p ν)) = hI.dpow k (p : T) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k = 0
    · rw [hk, (dpWν W p ν hW).dpow_zero (p_mem_Jν W p ν), hI.dpow_zero hpI, map_one]
    obtain ⟨e, hle, hc, heq⟩ := dpow_split p (dpWν W p ν hW) (p_mem_Jν W p ν) hk
    have hlt : k - p ^ e < k := Nat.sub_lt (Nat.pos_of_ne_zero hk)
      (pow_pos (Fact.out : p.Prime).pos _)
    have hT : IsUnit (choose k (p ^ e) : T) := by
      rw [← map_natCast (algebraMap W T)]; exact (hW _ hc).map _
    apply hT.mul_left_cancel
    have h2 := congrArg (lift W p ν hI hpI hnil) heq
    rw [map_mul, map_mul, map_natCast, lift_dpow_pow W p ν hW hI hpI hnil, ih _ hlt] at h2
    rw [h2, hI.mul_dpow hpI, Nat.add_sub_cancel' hle]

include hW in
theorem isDPMorphism_lift :
    DividedPowers.IsDPMorphism (dpWν W p ν hW) hI (lift W p ν hI hpI hnil : Wν W p ν →+* T) := by
  have hS : (Ibar W p ν).map (Ideal.Quotient.mk (Kp W p ν)) =
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Kp W p ν) (Lam W p ν i)) := by
    rw [Ibar, Ideal.map_span, ← Set.range_comp]; rfl
  refine DividedPowers.IsDPMorphism.on_span (dpWν W p ν hW) hI hS ?_ ?_
  · rintro _ ⟨i, rfl⟩
    rw [RingHom.coe_coe, lift_Lam]
    exact hI.dpow_mem (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hpI
  · rintro n _ ⟨i, rfl⟩
    simp only [RingHom.coe_coe]
    rw [lift_Lam, ← dpWν_p W p ν hW, (dpWν W p ν hW).dpow_comp
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (p_mem_Jν W p ν), map_mul, map_natCast,
      lift_dpow W p ν hW, hI.dpow_comp (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hpI]

end Lift

include hW in
/-- **Universality (page 4).** `W^{(ν)}`, with the divided powers `dpWν` on `J = (Λ₀, …, Λ_ν)`,
is initial among `W`-algebras `T` with a divided-power ideal `(I, γ)` such that `p ∈ I` and
`γ_n(p) = 0` for `n ≥ p^{ν+1}`: there is exactly one `W`-algebra map `W^{(ν)} → T` compatible
with the divided powers. -/
theorem universal {T : Type*} [CommRing T] [Algebra W T] {I : Ideal T} (hI : DividedPowers I)
    (hpI : (p : T) ∈ I) (hnil : ∀ n, p ^ (ν + 1) ≤ n → hI.dpow n (p : T) = 0) :
    ∃! f : Wν W p ν →ₐ[W] T,
      DividedPowers.IsDPMorphism (dpWν W p ν hW) hI (f : Wν W p ν →+* T) := by
  refine ⟨lift W p ν hI hpI hnil, isDPMorphism_lift W p ν hW hI hpI hnil, fun g hg => ?_⟩
  refine Ideal.Quotient.algHom_ext W (Ideal.Quotient.algHom_ext W (MvPolynomial.algHom_ext
    fun i => ?_))
  change g (Ideal.Quotient.mk _ (Lam W p ν i)) = lift W p ν hI hpI hnil
    (Ideal.Quotient.mk _ (Lam W p ν i))
  rw [lift_Lam, ← dpWν_p W p ν hW]
  have := hg.map_dpow (n := p ^ (i : ℕ)) (p_mem_Jν W p ν)
  rw [RingHom.coe_coe] at this
  rw [this, map_natCast g p]

end Universal

section Sufficiency

/-! ### The sufficiency half of the lemma of page 5

With `λᵢ ∈ W` the usual divided powers of `p` (any family with `λ₀ = p` and
`λᵢ^p = qᵢλᵢ₊₁`, such as `p^{p^i}/(p^i)!` in `W(k)`) and `Θᵢ = Λᵢ − λᵢ`, one has
`p^i Θᵢ = 0` in `W^{(ν)}` and `p^ν λ_ν^p = 0`. -/

variable [Fact p.Prime] (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (lam : ℕ → W)
  (hlam0 : lam 0 = p) (hlam : ∀ i, lam i ^ p = q p i * lam (i + 1))

/-- `Θᵢ = Λᵢ − λᵢ` in `A^{(ν)}`; its image in `W^{(ν)} = A^{(ν)}/(Λ₀ − p)` is the `Θᵢ` of
page 5. -/
noncomputable def Θ (i : Fin (ν + 1)) : Aν W p ν := Lam W p ν i - algebraMap W _ (lam i)

/-- `qᵢ = p · rᵢ` with `rᵢ` prime to `p` (`v_p(qᵢ) = 1`). -/
theorem q_eq_p_mul (i : ℕ) : ∃ r : ℕ, ¬ p ∣ r ∧ q p i = p * r := by
  have hq : q p i ≠ 0 := by
    intro h; have := factorial_eq_mul_q p i; rw [h, mul_zero] at this
    exact factorial_ne_zero _ this
  obtain ⟨r, hr⟩ : p ∣ q p i := by
    have := padicValNat_q p i
    exact dvd_of_one_le_padicValNat (by omega)
  refine ⟨r, fun hd => ?_, hr⟩
  obtain ⟨s, rfl⟩ := hd
  have h2 : p ^ 2 ∣ q p i := ⟨s, by rw [hr]; ring⟩
  have := (padicValNat_dvd_iff_le hq).mp h2
  rw [padicValNat_q] at this
  omega

include hW hlam0 hlam in
/-- **`p^i Θᵢ = 0` in `W^{(ν)}`** (page 6, by induction on `i`): `p^i Θᵢ ∈ (Λ₀ − p)`. -/
theorem p_pow_mul_Θ_mem (i : Fin (ν + 1)) :
    (p : Aν W p ν) ^ (i : ℕ) * Θ W p ν lam i ∈ Kp W p ν := by
  induction i using Fin.induction with
  | zero =>
    rw [Fin.val_zero, pow_zero, one_mul, Θ, show ((0 : Fin (ν + 1)) : ℕ) = 0 from rfl, hlam0,
      map_natCast]
    exact Ideal.mem_span_singleton_self _
  | succ i ih =>
    obtain ⟨r, hr, hq⟩ := q_eq_p_mul p i
    obtain ⟨u, hu⟩ := hW r hr
    -- `Λᵢ^p − λᵢ^p = qᵢ Θᵢ₊₁`, and `Θᵢ` divides it
    have h1 : Lam W p ν i.castSucc ^ p - algebraMap W (Aν W p ν) (lam i) ^ p =
        (q p i : Aν W p ν) * Θ W p ν lam i.succ := by
      rw [Lam_pow_castSucc, Θ, ← map_pow, hlam, map_mul, map_natCast, Fin.val_succ]
      ring
    obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (Lam W p ν i.castSucc) (algebraMap W (Aν W p ν) (lam i)) p
    have h2 : (p : Aν W p ν) ^ (i : ℕ) * ((q p i : Aν W p ν) * Θ W p ν lam i.succ) ∈ Kp W p ν := by
      rw [← h1, hS, ← mul_assoc]
      exact Ideal.mul_mem_right _ _ ih
    rw [hq, Nat.cast_mul, ← map_natCast (algebraMap W (Aν W p ν)) r, ← hu] at h2
    have h3 := Ideal.mul_mem_left _ (algebraMap W (Aν W p ν) ↑u⁻¹) h2
    rw [Fin.val_succ, pow_succ]
    convert h3 using 1
    have hv : algebraMap W (Aν W p ν) ↑u⁻¹ * algebraMap W (Aν W p ν) ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-((p : Aν W p ν) ^ (i : ℕ) * p * Θ W p ν lam i.succ)) * hv

include hW hlam0 hlam in
/-- **`p^ν λ_ν^p = 0` in `W^{(ν)}`** (page 6): `p^ν λ_ν^p ∈ (Λ₀ − p)`. -/
theorem p_pow_mul_lam_pow_mem :
    (p : Aν W p ν) ^ ν * algebraMap W (Aν W p ν) (lam ν) ^ p ∈ Kp W p ν := by
  obtain ⟨S, hS⟩ := sub_dvd_pow_sub_pow (Lam W p ν (Fin.last ν))
    (algebraMap W (Aν W p ν) (lam ν)) p
  have h := p_pow_mul_Θ_mem W p ν hW lam hlam0 hlam (Fin.last ν)
  rw [Fin.val_last] at h
  have h2 := Ideal.mul_mem_right (-S) _ h
  convert h2 using 1
  have hL := Lam_last_pow W p ν
  rw [Θ, Fin.val_last]
  linear_combination (-(p : Aν W p ν) ^ ν) * hS + (p : Aν W p ν) ^ ν * hL

include hW hlam0 hlam in
/-- If `λ_ν = p^m u`, `u` a unit, then `p^{ν + pm} = 0` in `W^{(ν)}`; for the usual
`λ_ν = p^{p^ν}/(p^ν)!`, `m = p^ν − (p^ν − 1)/(p − 1)` and `ν + pm = c(ν)`. -/
theorem p_pow_mem_Kp {m : ℕ} {u : W} (hu : IsUnit u) (hm : lam ν = p ^ m * u) :
    (p : Aν W p ν) ^ (ν + p * m) ∈ Kp W p ν := by
  have h := p_pow_mul_lam_pow_mem W p ν hW lam hlam0 hlam
  obtain ⟨v, rfl⟩ := hu
  have h3 := Ideal.mul_mem_left _ (algebraMap W (Aν W p ν) (↑v⁻¹ ^ p)) h
  convert h3 using 1
  have hv : (algebraMap W (Aν W p ν) ↑v⁻¹ * algebraMap W (Aν W p ν) ↑v) ^ p = 1 := by
    rw [← map_mul, Units.inv_mul, map_one, one_pow]
  rw [hm]
  simp only [map_mul, map_pow, map_natCast]
  linear_combination (-(p : Aν W p ν) ^ (ν + p * m)) * hv

end Sufficiency

/-- The hypotheses hold for `W = ℤ_p` (`k = 𝔽_p`): integers prime to `p` are units. -/
theorem padicInt_isUnit_natCast [Fact p.Prime] (n : ℕ) (hn : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn ?_)
  have := (PadicInt.norm_int_lt_one_iff_dvd (p := p) n).mp (by exact_mod_cast h)
  exact_mod_cast this

end Grothendieck.Folder5

/-!
## The necessity half of the lemma of page 5: the normal form of `W^{(ν)}` in the `Θᵢ`

Added 2026-10-25 (finding `5-universal-artinian-pd-normal-form`). Same hypotheses as above:
`W` a domain of characteristic zero in which the integers prime to `p` are units, `λᵢ ∈ W` with
`λ₀ = p`, `λᵢ^p = qᵢλᵢ₊₁` and `λ_ν = p^m · unit`, `Θᵢ = Λᵢ − λᵢ`, `c(ν) = ν + p m`. For a box
exponent `a` (`0 ≤ aᵢ < p`), `ord a` is the first index `i` with `aᵢ ≠ 0`, or `c(ν)` if `a = 0`.

* `Θ_pow_castSucc`, `Θ_pow_last`: `Θᵢ^p = qᵢΘᵢ₊₁ − Σ_{0<k<p} C(p,k)λᵢ^{p−k}Θᵢ^k` and
  `Θ_ν^p = −λ_ν^p − Σ_{0<k<p} C(p,k)λ_ν^{p−k}Θ_ν^k` (the carry of page 8, in the `Θᵢ`);
* `Θ_mul_tmono_mem`, `mul_mem_S`: the `W`-span `S_n` of the `p^{min(ord a, n)} Θ^a` is an
  ideal of `A^{(ν)}` — the verification the page leaves to the reader, by descending induction on
  the index of the factor `Θⱼ`, using only `v_p(qᵢ) ≥ 1`;
* `span_tmono`, `tmono_linearIndependent`: the `Θ^a` form a basis of `A^{(ν)}` (they span, by
  `S_0 = A^{(ν)}`; a surjective endomorphism of a finite module over a commutative ring is
  injective, against the basis `Λ^a`, `mono_linearIndependent`);
* **`normalForm`** (the lemma of page 5, both halves): `Σ w_a Θ^a ∈ (Θ₀) = (Λ₀ − p)` iff
  `p^{ord a} ∣ w_a` for every `a` (`Kp_le_S`, `S_le_Kp`);
* **`WνEquiv`** (the corollary of page 6): `W^{(ν)} ≃ ⊕_a W/p^{ord a}` as `W`-modules;
* **`p_pow_eq_zero_iff`**: if `p` is not a unit, `p^k = 0` in `W^{(ν)}` iff `k ≥ c(ν)`;
* **`length_Wν`, `length_Wν_eq`**: over a discrete valuation ring with uniformiser `p`, `W^{(ν)}`
  has length `Σ_a ord a = p + p² + ⋯ + p^ν + p m` (`sum_ord`), which equals the reading's
  `c(ν) + Σ_{i=1}^{ν} i(p−1)p^{ν−i}`;
* `exists_lamStd`, `p_pow_eq_zero_iff_std`, `length_Wν_std`, `padicInt_Wν`: with the usual
  `λᵢ = p^{p^i}/(p^i)!`, `m = p^ν − v_p((p^ν)!)`; for `W = ℤ_p` the order of `1` is exactly
  `p^{c(ν)}` and the length is `p + ⋯ + p^ν + p(p^ν − v_p((p^ν)!))` (4 for `p = 2`, `ν = 1`).

Not formalised: the quotients `W^{(ν,r)}` of page 7.
-/

namespace Grothendieck.Folder5

open Nat MvPolynomial

section NormalForm

variable (p ν : ℕ)

open Classical in
/-- The weight of a box exponent `a`: the first index `i` with `aᵢ ≠ 0`, or `c` if `a = 0`. -/
noncomputable def ord (c : ℕ) (a : Fin (ν + 1) → Fin p) : ℕ :=
  if h : ∃ k, ∃ i : Fin (ν + 1), (i : ℕ) = k ∧ (a i : ℕ) ≠ 0 then Nat.find h else c

variable {p ν} {c : ℕ}

theorem ord_le {a : Fin (ν + 1) → Fin p} {i : Fin (ν + 1)} (hi : (a i : ℕ) ≠ 0) : ord p ν c a ≤ i := by
  have h : ∃ k, ∃ j : Fin (ν + 1), (j : ℕ) = k ∧ (a j : ℕ) ≠ 0 := ⟨i, i, rfl, hi⟩
  classical
  simp only [ord, h, ↓reduceDIte]
  exact Nat.find_min' h ⟨i, rfl, hi⟩

theorem ord_spec {a : Fin (ν + 1) → Fin p} {i : Fin (ν + 1)} (hi : (a i : ℕ) ≠ 0) :
    ∃ j : Fin (ν + 1), (j : ℕ) = ord p ν c a ∧ (a j : ℕ) ≠ 0 := by
  have h : ∃ k, ∃ j : Fin (ν + 1), (j : ℕ) = k ∧ (a j : ℕ) ≠ 0 := ⟨i, i, rfl, hi⟩
  classical
  simp only [ord, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem ord_of_forall {a : Fin (ν + 1) → Fin p} (h : ∀ i, (a i : ℕ) = 0) : ord p ν c a = c := by
  classical
  simp only [ord, dite_eq_right_iff]
  rintro ⟨k, i, -, hi⟩
  exact absurd (h i) hi

theorem ord_le_max (a : Fin (ν + 1) → Fin p) : ord p ν c a ≤ ν ∨ ord p ν c a = c := by
  by_cases h : ∃ i, (a i : ℕ) ≠ 0
  · obtain ⟨i, hi⟩ := h
    obtain ⟨j, hj, -⟩ := ord_spec (c := c) hi
    exact Or.inl (hj ▸ Nat.lt_succ_iff.mp j.2)
  · exact Or.inr (ord_of_forall (by simpa using h))

/-- Changing one exponent `aⱼ` does not raise the weight past `ord a` unless `ord a = j`. -/
theorem ord_update_le {a : Fin (ν + 1) → Fin p} {j : Fin (ν + 1)} (hj : (a j : ℕ) ≠ 0) (v : Fin p)
    (h : (ord p ν c a : ℕ) ≠ j) : ord p ν c (Function.update a j v) ≤ ord p ν c a := by
  obtain ⟨i, hi, hai⟩ := ord_spec (c := c) hj
  have hij : i ≠ j := fun e => h (by rw [← hi, e])
  rw [← hi]
  exact ord_le (by rwa [Function.update_of_ne hij])

theorem ord_update_le' {a : Fin (ν + 1) → Fin p} {j : Fin (ν + 1)} {v : Fin p} (hv : (v : ℕ) ≠ 0)
    (hc : ν ≤ c) : ord p ν c (Function.update a j v) ≤ ord p ν c a := by
  have hb : (Function.update a j v j : ℕ) ≠ 0 := by rwa [Function.update_self]
  by_cases ha : ∃ i, (a i : ℕ) ≠ 0
  · obtain ⟨i, hai⟩ := ha
    obtain ⟨k, hk, hak⟩ := ord_spec (c := c) hai
    by_cases hkj : k = j
    · rw [← hk, hkj]; exact ord_le hb
    · rw [← hk]; exact ord_le (by rwa [Function.update_of_ne hkj])
  · push Not at ha
    rw [ord_of_forall ha]
    exact (ord_le hb).trans (by have := j.2; omega)


end NormalForm

section ThetaBasis

variable (W : Type*) [CommRing W] (p ν : ℕ) (lam : ℕ → W)

/-- The monomial `Θ^a = Θ₀^{a₀} ⋯ Θ_ν^{a_ν}`, `0 ≤ aᵢ < p`. -/
noncomputable def tmono (a : Fin (ν + 1) → Fin p) : Aν W p ν := ∏ i, Θ W p ν lam i ^ (a i : ℕ)

theorem tmono_eq (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) :
    tmono W p ν lam a = Θ W p ν lam j ^ (a j : ℕ) *
      ∏ i ∈ Finset.univ.erase j, Θ W p ν lam i ^ (a i : ℕ) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

theorem tmono_update (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) (v : Fin p) :
    tmono W p ν lam (Function.update a j v) = Θ W p ν lam j ^ (v : ℕ) *
      ∏ i ∈ Finset.univ.erase j, Θ W p ν lam i ^ (a i : ℕ) := by
  rw [tmono_eq W p ν lam _ j, Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem tmono_zero (a : Fin (ν + 1) → Fin p) (h : ∀ i, (a i : ℕ) = 0) : tmono W p ν lam a = 1 :=
  Finset.prod_eq_one fun i _ => by rw [h i, pow_zero]

theorem Lam_eq_Θ (i : Fin (ν + 1)) :
    Lam W p ν i = Θ W p ν lam i + algebraMap W (Aν W p ν) (lam i) := by
  rw [Θ]; ring

/-- The binomial expansion of `Λᵢ^p = (Θᵢ + λᵢ)^p`. -/
theorem Θ_pow (hp : 0 < p) (i : Fin (ν + 1)) :
    Θ W p ν lam i ^ p = Lam W p ν i ^ p - algebraMap W (Aν W p ν) (lam i) ^ p -
      ∑ k ∈ Finset.Ico 1 p, ((p.choose k : W) * lam i ^ (p - k)) • Θ W p ν lam i ^ k := by
  rw [Lam_eq_Θ W p ν lam, add_pow, Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hp]
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
    Nat.sub_self, Nat.choose_self, zero_add]
  have : ∑ k ∈ Finset.Ico 1 p, Θ W p ν lam i ^ k * algebraMap W (Aν W p ν) (lam i) ^ (p - k) *
      (p.choose k : Aν W p ν) =
      ∑ k ∈ Finset.Ico 1 p, ((p.choose k : W) * lam i ^ (p - k)) • Θ W p ν lam i ^ k :=
    Finset.sum_congr rfl fun k _ => by
      rw [Algebra.smul_def (R := W) (A := Aν W p ν), map_mul, map_natCast, map_pow]; ring
  rw [this]; ring

/-- `Θᵢ^p = qᵢΘᵢ₊₁ − Σ_{0<k<p} C(p,k) λᵢ^{p−k} Θᵢ^k` for `i < ν`. -/
theorem Θ_pow_castSucc (hp : 0 < p) (hlam : ∀ i, lam i ^ p = q p i * lam (i + 1)) (i : Fin ν) :
    Θ W p ν lam i.castSucc ^ p = (q p i : W) • Θ W p ν lam i.succ -
      ∑ k ∈ Finset.Ico 1 p, ((p.choose k : W) * lam i ^ (p - k)) •
        Θ W p ν lam i.castSucc ^ k := by
  rw [Θ_pow W p ν lam hp, Lam_pow_castSucc, Lam_eq_Θ W p ν lam i.succ, Fin.val_castSucc,
    ← map_pow, hlam, Fin.val_succ, Algebra.smul_def (R := W) (A := Aν W p ν), map_mul, map_natCast]
  ring

/-- `Θ_ν^p = −λ_ν^p − Σ_{0<k<p} C(p,k) λ_ν^{p−k} Θ_ν^k`. -/
theorem Θ_pow_last (hp : 0 < p) :
    Θ W p ν lam (Fin.last ν) ^ p = -algebraMap W (Aν W p ν) (lam ν ^ p) -
      ∑ k ∈ Finset.Ico 1 p, ((p.choose k : W) * lam ν ^ (p - k)) •
        Θ W p ν lam (Fin.last ν) ^ k := by
  rw [Θ_pow W p ν lam hp, Lam_last_pow, Fin.val_last, map_pow]
  ring

/-- `S_n`, the `W`-span of the `p^{min(ord a, n)} Θ^a`; `S_0` is the span of the `Θ^a` and
`S_c` the lattice of the lemma of page 5. -/
noncomputable def S (c n : ℕ) : Submodule W (Aν W p ν) :=
  Submodule.span W (Set.range fun a => (p : W) ^ min (ord p ν c a) n • tmono W p ν lam a)

theorem mem_S {c n k : ℕ} (b : Fin (ν + 1) → Fin p) (hk : min (ord p ν c b) n ≤ k) :
    (p : W) ^ k • tmono W p ν lam b ∈ S W p ν lam c n := by
  rw [← Nat.sub_add_cancel hk, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem pow_mul_tmono_update (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) {k : ℕ} (hk : k < p) :
    Θ W p ν lam j ^ k * tmono W p ν lam (Function.update a j ⟨0, by omega⟩) =
      tmono W p ν lam (Function.update a j ⟨k, hk⟩) := by
  rw [tmono_update, tmono_update, pow_zero, one_mul]

variable {W p ν lam}

theorem smul_mem_S_of {c n e : ℕ} {y : Aν W p ν} (e' : ℕ) (he : e' ≤ e)
    (hy : (p : W) ^ e' • y ∈ S W p ν lam c n) : (p : W) ^ e • y ∈ S W p ν lam c n := by
  rw [← Nat.sub_add_cancel he, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ hy

variable [Fact p.Prime]

/-- The terms `C(p,k) λⱼ^{p−k} Θⱼ^k Θ^{a'}`, `0 < k < p`, of the carry stay in `S_n`. -/
theorem carry_sum_mem {m n : ℕ} (a : Fin (ν + 1) → Fin p) (j : Fin (ν + 1)) (μ : W)
    (hoj : ord p ν (ν + p * m) a ≤ j) :
    (p : W) ^ min (min (ord p ν (ν + p * m) a) j) n •
      ∑ k ∈ Finset.Ico 1 p, ((p.choose k : W) * μ ^ (p - k)) •
        (Θ W p ν lam j ^ k * tmono W p ν lam
          (Function.update a j ⟨0, (Fact.out : p.Prime).pos⟩)) ∈
      S W p ν lam (ν + p * m) n := by
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨hk1, hkp⟩ := Finset.mem_Ico.mp hk
  rw [pow_mul_tmono_update W p ν lam a j hkp, smul_comm]
  refine Submodule.smul_mem _ _ (mem_S W p ν lam _ ?_)
  have := ord_update_le' (c := ν + p * m) (a := a) (j := j) (v := ⟨k, hkp⟩)
    (by simp only; omega) (Nat.le_add_right _ _)
  omega

/-- **The carry**: `p^{min(ord a, j, n)} Θⱼ Θ^a ∈ S_n`, by descending induction on `j`. -/
theorem Θ_mul_tmono_mem (hlam : ∀ i, lam i ^ p = q p i * lam (i + 1)) {m : ℕ} {u : W}
    (hm : lam ν = p ^ m * u) (n : ℕ) (j : Fin (ν + 1)) (a : Fin (ν + 1) → Fin p) :
    (p : W) ^ min (min (ord p ν (ν + p * m) a) j) n • (Θ W p ν lam j * tmono W p ν lam a) ∈
      S W p ν lam (ν + p * m) n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hc : ν ≤ ν + p * m := Nat.le_add_right _ _
  -- the case `aⱼ + 1 < p`: no carry
  have small : ∀ (j : Fin (ν + 1)) (a : Fin (ν + 1) → Fin p), (a j : ℕ) + 1 < p →
      (p : W) ^ min (min (ord p ν (ν + p * m) a) j) n • (Θ W p ν lam j * tmono W p ν lam a) ∈
        S W p ν lam (ν + p * m) n := by
    intro j a h
    rw [tmono_eq W p ν lam a j, ← mul_assoc, ← _root_.pow_succ',
      show (a j : ℕ) + 1 = ((⟨_, h⟩ : Fin p) : ℕ) from rfl, ← tmono_update]
    apply mem_S
    have h1 := ord_le (c := ν + p * m) (a := Function.update a j ⟨_, h⟩) (i := j)
      (by rw [Function.update_self]; simp)
    have h2 := ord_update_le' (c := ν + p * m) (a := a) (j := j) (v := ⟨_, h⟩) (by simp) hc
    omega
  -- the case `aⱼ = p − 1`: `Θⱼ Θ^a = Θⱼ^p Θ^{a'}`
  have big : ∀ (j : Fin (ν + 1)) (a : Fin (ν + 1) → Fin p), (a j : ℕ) + 1 = p →
      Θ W p ν lam j * tmono W p ν lam a =
        Θ W p ν lam j ^ p * tmono W p ν lam (Function.update a j ⟨0, hp⟩) := by
    intro j a h
    rw [tmono_eq W p ν lam a j, tmono_update, ← mul_assoc, ← _root_.pow_succ', h]
    simp
  induction j using Fin.reverseInduction generalizing a with
  | last =>
    by_cases h : (a (Fin.last ν) : ℕ) + 1 < p
    · exact small _ a h
    have h' : (a (Fin.last ν) : ℕ) + 1 = p := by have := (a (Fin.last ν)).2; omega
    have hne : (a (Fin.last ν) : ℕ) ≠ 0 := by omega
    have hoj := ord_le (c := ν + p * m) hne
    have hoa' := ord_update_le (c := ν + p * m) hne ⟨0, hp⟩
    have hoa'c : ord p ν (ν + p * m) (Function.update a (Fin.last ν) ⟨0, hp⟩) ≤ ν + p * m :=
      (ord_le_max _).elim (fun h => by omega) (fun h => h.le)
    rw [Fin.val_last] at hoj hoa'
    rw [big _ a h', Θ_pow_last W p ν lam hp, sub_mul, Finset.sum_mul, smul_sub]
    refine Submodule.sub_mem _ ?_ ?_
    · have e : -algebraMap W (Aν W p ν) (lam ν ^ p) *
          tmono W p ν lam (Function.update a (Fin.last ν) ⟨0, hp⟩) =
          -(u ^ p • ((p : W) ^ (p * m) • tmono W p ν lam (Function.update a (Fin.last ν) ⟨0, hp⟩))) := by
        rw [Algebra.smul_def (R := W) (A := Aν W p ν), Algebra.smul_def (R := W) (A := Aν W p ν), hm]
        simp only [map_mul, map_pow, map_natCast]
        ring
      rw [e, smul_neg, smul_comm ((p : W) ^ _) (u ^ p), smul_smul ((p : W) ^ _) ((p : W) ^ (p * m)),
        ← pow_add]
      refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (mem_S W p ν lam _ ?_))
      rw [Fin.val_last]
      omega
    · simp only [smul_mul_assoc]
      exact carry_sum_mem a _ _ (by rw [Fin.val_last]; exact hoj)
  | cast i ih =>
    by_cases h : (a i.castSucc : ℕ) + 1 < p
    · exact small _ a h
    have h' : (a i.castSucc : ℕ) + 1 = p := by have := (a i.castSucc).2; omega
    have hne : (a i.castSucc : ℕ) ≠ 0 := by omega
    have hoj := ord_le (c := ν + p * m) hne
    have hoa' := ord_update_le (c := ν + p * m) hne ⟨0, hp⟩
    rw [Fin.val_castSucc] at hoj hoa'
    rw [big _ a h', Θ_pow_castSucc W p ν lam hp hlam, sub_mul, Finset.sum_mul, smul_sub]
    refine Submodule.sub_mem _ ?_ ?_
    · obtain ⟨r, -, hq⟩ := q_eq_p_mul p i
      have hih := ih (Function.update a i.castSucc ⟨0, hp⟩)
      rw [Fin.val_succ] at hih
      have e : ((q p i : W) • Θ W p ν lam i.succ) *
          tmono W p ν lam (Function.update a i.castSucc ⟨0, hp⟩) =
          (r : W) • ((p : W) • (Θ W p ν lam i.succ *
            tmono W p ν lam (Function.update a i.castSucc ⟨0, hp⟩))) := by
        rw [smul_mul_assoc, hq, Nat.cast_mul, mul_comm (p : W), mul_smul]
      rw [e, smul_comm ((p : W) ^ _) (r : W), smul_smul ((p : W) ^ _) (p : W), ← _root_.pow_succ]
      refine Submodule.smul_mem _ _ (smul_mem_S_of _ ?_ hih)
      rw [Fin.val_castSucc]
      omega
    · simp only [smul_mul_assoc]
      exact carry_sum_mem a _ _ hoj

omit [Fact p.Prime] in
theorem ord_le_c {m : ℕ} (a : Fin (ν + 1) → Fin p) : ord p ν (ν + p * m) a ≤ ν + p * m :=
  (ord_le_max a).elim (fun h => by omega) (fun h => h.le)

variable (hlam : ∀ i, lam i ^ p = q p i * lam (i + 1)) {m : ℕ} {u : W} (hm : lam ν = p ^ m * u)

include hlam hm in
theorem Θ_mul_mem_S {n : ℕ} (j : Fin (ν + 1)) {x : Aν W p ν}
    (hx : x ∈ S W p ν lam (ν + p * m) n) : Θ W p ν lam j * x ∈ S W p ν lam (ν + p * m) n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [mul_smul_comm]
    exact smul_mem_S_of _ (by omega) (Θ_mul_tmono_mem hlam hm n j a)
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul w x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ w hx

include hlam hm in
/-- **`S_n` is an ideal** of `A^{(ν)}` (the point the page leaves to the reader, with a « ! »). -/
theorem mul_mem_S {n : ℕ} (y : Aν W p ν) {x : Aν W p ν}
    (hx : x ∈ S W p ν lam (ν + p * m) n) : y * x ∈ S W p ν lam (ν + p * m) n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction f using MvPolynomial.induction_on generalizing x with
  | C w =>
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk W, AlgHom.commutes,
      ← Algebra.smul_def]
    exact Submodule.smul_mem _ w hx
  | add f g hf hg => rw [map_add, add_mul]; exact Submodule.add_mem _ (hf hx) (hg hx)
  | mul_X f j hf =>
    rw [map_mul, mul_assoc]
    apply hf
    change Lam W p ν j * x ∈ _
    rw [Lam_eq_Θ W p ν lam, add_mul, ← Algebra.smul_def]
    exact Submodule.add_mem _ (Θ_mul_mem_S hlam hm j hx) (Submodule.smul_mem _ _ hx)

include hlam hm in
/-- The `Θ^a`, `0 ≤ aᵢ < p`, span `A^{(ν)}`. -/
theorem span_tmono : Submodule.span W (Set.range (tmono W p ν lam)) = ⊤ := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hS : S W p ν lam (ν + p * m) 0 = Submodule.span W (Set.range (tmono W p ν lam)) := by
    simp [S]
  rw [← hS, eq_top_iff]
  rintro y -
  have h1 : (1 : Aν W p ν) ∈ S W p ν lam (ν + p * m) 0 := by
    have := mem_S W p ν lam (c := ν + p * m) (n := 0) (k := 0) (fun _ => ⟨0, hp⟩) (by simp)
    rwa [pow_zero, one_smul, tmono_zero W p ν lam _ fun _ => rfl] at this
  simpa using mul_mem_S hlam hm y h1

omit [Fact p.Prime] in
/-- The box monomials `Λ^a` are linearly independent (the argument of `psi_injective`). -/
theorem mono_linearIndependent [IsDomain W] [CharZero W] :
    LinearIndependent W (mono W p ν) := by
  rw [Fintype.linearIndependent_iff]
  intro w hx
  set K := FractionRing W
  have hinj : Function.Injective (algebraMap W K) := IsFractionRing.injective W K
  set P : Polynomial K := ∑ a, Polynomial.C (algebraMap W K (w a) *
    ∏ i : Fin (ν + 1), cf p K (i : ℕ) ^ (a i : ℕ)) * Polynomial.X ^ deg p a with hP
  have hmk : Ideal.Quotient.mk _ P = psi W p ν K (∑ a, w a • mono W p ν a) := by
    simp only [hP, map_sum, map_mul, map_smul, psi_mono, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← algebraMap_smul K (w a), Algebra.smul_def (R := K) (A := Bν p ν K), xb,
      algebraMap_Bν, algebraMap_Bν]
    ring
  rw [hx, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    Polynomial.X_pow_dvd_iff] at hmk
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

include hlam hm in
/-- **The `Θ^a`, `0 ≤ aᵢ < p`, form a basis of `A^{(ν)}`**: they span, and a surjective
endomorphism of a finite module over a commutative ring is injective. -/
theorem tmono_linearIndependent [IsDomain W] [CharZero W] :
    LinearIndependent W (tmono W p ν lam) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [linearIndependent_iff_injective_fintypeLinearCombination]
  classical
  have : Module.Finite W (Aν W p ν) := ⟨⟨Finset.univ.image (mono W p ν), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact boxSpan_eq_top W p ν hp⟩⟩
  refine OrzechProperty.injective_of_surjective_of_injective
    (Fintype.linearCombination W (mono W p ν)) _ ?_ ?_
  · exact linearIndependent_iff_injective_fintypeLinearCombination.mp
      (mono_linearIndependent (W := W) (p := p) (ν := ν))
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_tmono hlam hm

include hlam hm in
theorem Θ_zero_mem_S (n : ℕ) : Θ W p ν lam 0 ∈ S W p ν lam (ν + p * m) n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have := Θ_mul_tmono_mem hlam hm n 0 (fun _ => ⟨0, hp⟩)
  rwa [tmono_zero W p ν lam _ fun _ => rfl, mul_one, Fin.val_zero, Nat.min_zero, Nat.zero_min,
    pow_zero, one_smul] at this

include hlam hm in
/-- **Necessity**: `(Λ₀ − p) ⊆ S_n`. -/
theorem Kp_le_S (hlam0 : lam 0 = p) (n : ℕ) {x : Aν W p ν} (hx : x ∈ Kp W p ν) :
    x ∈ S W p ν lam (ν + p * m) n := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  have h0 : Lam W p ν 0 - (p : Aν W p ν) = Θ W p ν lam 0 := by
    rw [Θ, Fin.val_zero, hlam0, map_natCast]
  rw [h0]
  exact mul_mem_S hlam hm y (Θ_zero_mem_S hlam hm n)

include hlam hm in
/-- **Sufficiency** (from `p_pow_mul_Θ_mem`, `p_pow_mem_Kp`): `S_c ⊆ (Λ₀ − p)`. -/
theorem S_le_Kp (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (hlam0 : lam 0 = p) (hu : IsUnit u)
    {x : Aν W p ν} (hx : x ∈ S W p ν lam (ν + p * m) (ν + p * m)) : x ∈ Kp W p ν := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    dsimp only
    rw [min_eq_left (ord_le_c a)]
    by_cases ha : ∃ i, (a i : ℕ) ≠ 0
    · obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj, haj⟩ := ord_spec (c := ν + p * m) hi
      rw [← hj, tmono_eq W p ν lam a j, ← Nat.sub_add_cancel (Nat.pos_of_ne_zero haj),
        _root_.pow_succ, Algebra.smul_def (R := W) (A := Aν W p ν), map_pow, map_natCast]
      have := p_pow_mul_Θ_mem W p ν hW lam hlam0 hlam j
      have e : (p : Aν W p ν) ^ (j : ℕ) * (Θ W p ν lam j ^ ((a j : ℕ) - 1) * Θ W p ν lam j *
          ∏ i ∈ Finset.univ.erase j, Θ W p ν lam i ^ (a i : ℕ)) =
          (p : Aν W p ν) ^ (j : ℕ) * Θ W p ν lam j * (Θ W p ν lam j ^ ((a j : ℕ) - 1) *
          ∏ i ∈ Finset.univ.erase j, Θ W p ν lam i ^ (a i : ℕ)) := by ring
      rw [e]
      exact Ideal.mul_mem_right _ _ this
    · push Not at ha
      rw [ord_of_forall ha, tmono_zero W p ν lam a ha, Algebra.smul_def (R := W) (A := Aν W p ν),
        mul_one, map_pow, map_natCast]
      exact p_pow_mem_Kp W p ν hW lam hlam0 hlam hu hm
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul w x _ hx =>
    rw [Algebra.smul_def (R := W) (A := Aν W p ν)]
    exact Ideal.mul_mem_left _ _ hx

include hlam hm in
/-- **The lemma of page 5** (both halves). For `w : box → W`, `Σ_a w_a Θ^a ∈ (Λ₀ − p)` iff
`p^{ord a} ∣ w_a` for every `a`: `p^i ∣ w_a` when `aᵢ` is the first nonzero exponent, and
`p^{c(ν)} ∣ w_0`, `c(ν) = ν + p m`, `λ_ν = p^m · unit`. -/
theorem normalForm [IsDomain W] [CharZero W] (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))
    (hlam0 : lam 0 = p) (hu : IsUnit u) (w : (Fin (ν + 1) → Fin p) → W) :
    ∑ a, w a • tmono W p ν lam a ∈ Kp W p ν ↔
      ∀ a, (p : W) ^ ord p ν (ν + p * m) a ∣ w a := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun W).mp
      (Kp_le_S hlam hm hlam0 (ν + p * m) h)
    have := (Fintype.linearIndependent_iffₛ.mp (tmono_linearIndependent hlam hm)) w
      (fun a => v a * (p : W) ^ min (ord p ν (ν + p * m) a) (ν + p * m))
      (by rw [← hv]; simp_rw [smul_smul])
    intro a
    rw [this a, min_eq_left (ord_le_c a)]
    exact dvd_mul_left _ _
  · intro h
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨t, ht⟩ := h a
    rw [ht, mul_comm, mul_smul]
    refine Submodule.smul_of_tower_mem _ t (S_le_Kp hlam hm hW hlam0 hu (mem_S W p ν lam a ?_))
    exact min_le_left _ _

include hlam hm in
/-- **The exact order of `1`**: `p^k = 0` in `W^{(ν)}` iff `k ≥ c(ν) = ν + p m`, when `p` is not
a unit of `W`. -/
theorem p_pow_eq_zero_iff [IsDomain W] [CharZero W] (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))
    (hlam0 : lam 0 = p) (hu : IsUnit u) (hpu : ¬ IsUnit (p : W)) (k : ℕ) :
    (p : Wν W p ν) ^ k = 0 ↔ ν + p * m ≤ k := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set a0 : Fin (ν + 1) → Fin p := fun _ => ⟨0, hp⟩
  have hsum : ∑ a, (Pi.single a0 ((p : W) ^ k) : (Fin (ν + 1) → Fin p) → W) a •
      tmono W p ν lam a = (p : Aν W p ν) ^ k := by
    rw [Fintype.sum_eq_single a0 (fun a ha => by rw [Pi.single_eq_of_ne ha, zero_smul]),
      Pi.single_eq_same, tmono_zero W p ν lam a0 fun _ => rfl,
      Algebra.smul_def (R := W) (A := Aν W p ν), mul_one,
      map_pow, map_natCast]
  rw [← map_natCast (Ideal.Quotient.mk (Kp W p ν)), ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    ← hsum, normalForm hlam hm hW hlam0 hu]
  have hp0 : (p : W) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  constructor
  · intro h
    have := h a0
    rwa [Pi.single_eq_same, ord_of_forall (fun _ => rfl), pow_dvd_pow_iff hp0 hpu] at this
  · intro hk a
    by_cases ha : a = a0
    · rw [ha, Pi.single_eq_same, ord_of_forall (fun _ => rfl)]
      exact pow_dvd_pow _ hk
    · rw [Pi.single_eq_of_ne ha]
      exact dvd_zero _

include hlam hm in
/-- The coordinates in the basis `Θ^a`: `(w_a) ↦ Σ_a w_a Θ^a`, an isomorphism `W^{box} ≃ A^{(ν)}`. -/
noncomputable def tmonoEquiv [IsDomain W] [CharZero W] :
    ((Fin (ν + 1) → Fin p) → W) ≃ₗ[W] Aν W p ν :=
  LinearEquiv.ofBijective (Fintype.linearCombination W (tmono W p ν lam))
    ⟨linearIndependent_iff_injective_fintypeLinearCombination.mp (tmono_linearIndependent hlam hm),
      by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]; exact span_tmono hlam hm⟩

include hlam hm in
theorem map_Kp_tmonoEquiv_symm [IsDomain W] [CharZero W] (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))
    (hlam0 : lam 0 = p) (hu : IsUnit u) :
    ((Kp W p ν).restrictScalars W).map (tmonoEquiv hlam hm).symm.toLinearMap =
      Submodule.pi Set.univ fun a => Ideal.span {(p : W) ^ ord p ν (ν + p * m) a} := by
  ext v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.restrictScalars_mem]
  change Fintype.linearCombination W (tmono W p ν lam) v ∈ Kp W p ν ↔ _
  rw [Fintype.linearCombination_apply, normalForm hlam hm hW hlam0 hu]
  simp [Submodule.mem_pi, Ideal.mem_span_singleton]

include hlam hm in
/-- **The corollary of page 6 (normal form of `W^{(ν)}`).** As a `W`-module,
`W^{(ν)} ≃ ⊕_a W/p^{ord a}`, `a` over the box `0 ≤ aᵢ < p`: every element is uniquely
`Σ_a w_a Θ^a` with `w_a` taken mod `p^i` when `aᵢ` is the first nonzero exponent and `w_0` mod
`p^{c(ν)}` (and `w_a = 0` when `a₀ ≠ 0`). -/
noncomputable def WνEquiv [IsDomain W] [CharZero W] (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))
    (hlam0 : lam 0 = p) (hu : IsUnit u) :
    Wν W p ν ≃ₗ[W] ((a : Fin (ν + 1) → Fin p) → W ⧸ Ideal.span {(p : W) ^ ord p ν (ν + p * m) a}) :=
  (Submodule.Quotient.restrictScalarsEquiv W (Kp W p ν)).symm ≪≫ₗ
    Submodule.Quotient.equiv _ _ (tmonoEquiv hlam hm).symm
      (map_Kp_tmonoEquiv_symm hlam hm hW hlam0 hu) ≪≫ₗ
    Submodule.quotientPi _

include hlam hm in
/-- **The length of `W^{(ν)}`** over a discrete valuation ring `W` with uniformiser `p`
(`W(k)`, `ℤ_p`): `Σ_a ord a`. -/
theorem length_Wν [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (hlam0 : lam 0 = p) (hu : IsUnit u)
    (hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)}) :
    Module.length W (Wν W p ν) = ∑ a : Fin (ν + 1) → Fin p, (ord p ν (ν + p * m) a : ℕ∞) := by
  rw [(WνEquiv hlam hm hW hlam0 hu).length_eq, Module.length_pi_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Ideal.span_singleton_pow, ← hmax,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

section Count

variable {p : ℕ}

theorem ord_cons {ν c : ℕ} (hc : ν + 1 ≤ c) (x : Fin p) (a : Fin (ν + 1) → Fin p) :
    ord p (ν + 1) c (Fin.cons x a : Fin (ν + 1 + 1) → Fin p) =
      if (x : ℕ) = 0 then ord p ν (c - 1) a + 1 else 0 := by
  split_ifs with hx
  · by_cases ha : ∃ i, (a i : ℕ) ≠ 0
    · obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj, haj⟩ := ord_spec (c := c - 1) hi
      have hj' : ((Fin.cons x a : Fin (ν + 1 + 1) → Fin p) j.succ : ℕ) ≠ 0 := by
        rwa [Fin.cons_succ]
      have h1 := ord_le (c := c) hj'
      obtain ⟨k, hk, hak⟩ := ord_spec (c := c) hj'
      have h2 : ord p ν (c - 1) a + 1 ≤ ord p (ν + 1) c (Fin.cons x a) := by
        rw [← hk]
        cases k using Fin.cases with
        | zero => rw [Fin.cons_zero] at hak; exact absurd hx hak
        | succ k =>
          rw [Fin.cons_succ] at hak
          have := ord_le (c := c - 1) hak
          simp only [Fin.val_succ]; omega
      simp only [Fin.val_succ] at h1
      omega
    · push Not at ha
      rw [ord_of_forall ha, ord_of_forall]
      · omega
      · intro i
        cases i using Fin.cases with
        | zero => rwa [Fin.cons_zero]
        | succ i => rw [Fin.cons_succ]; exact ha i
  · have h0 : ((Fin.cons x a : Fin (ν + 1 + 1) → Fin p) 0 : ℕ) ≠ 0 := by rwa [Fin.cons_zero]
    have := ord_le (c := c) h0
    simp only [Fin.val_zero] at this
    omega

/-- **The count**: `Σ_a ord a + ν + 1 = (1 + p + ⋯ + p^ν) + c`, `a` over the box. -/
theorem sum_ord (hp : 0 < p) (ν c : ℕ) (hc : ν ≤ c) :
    ∑ a : Fin (ν + 1) → Fin p, ord p ν c a + ν + 1 = ∑ j ∈ Finset.range (ν + 1), p ^ j + c := by
  induction ν generalizing c with
  | zero =>
    have h : ∀ a : Fin 1 → Fin p, ord p 0 c a = if (a 0 : ℕ) = 0 then c else 0 := by
      intro a
      split_ifs with ha
      · exact ord_of_forall fun i => by rwa [Fin.fin_one_eq_zero i]
      · have := ord_le (c := c) ha
        simp only [Fin.val_zero] at this
        omega
    simp_rw [h]
    rw [Fintype.sum_eq_single (fun _ => ⟨0, hp⟩) fun a ha => ?_]
    · have e : ((fun _ => (⟨0, hp⟩ : Fin p)) (0 : Fin 1) : ℕ) = 0 := rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true e), Finset.sum_range_one, pow_zero]
      omega
    · exact ite_eq_right_iff.mpr fun h0 =>
        absurd (_root_.funext fun i => by rw [Fin.fin_one_eq_zero i]; exact Fin.ext h0) ha
  | succ ν ih =>
    rw [← (Fin.consEquiv fun _ => Fin p).sum_comp, Fintype.sum_prod_type]
    have hcons : ∀ (x : Fin p) (a : Fin (ν + 1) → Fin p),
        (Fin.consEquiv fun _ => Fin p) (x, a) = Fin.cons x a :=
      fun x a => _root_.funext fun i => Fin.consEquiv_apply _ _ i
    simp_rw [hcons, ord_cons (by omega : ν + 1 ≤ c)]
    rw [Fintype.sum_eq_single (⟨0, hp⟩ : Fin p) fun x hx => ?_]
    · simp only [↓reduceIte]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_range_succ _ (ν + 1)]
      have := ih (c - 1) (by omega)
      omega
    · have : (x : ℕ) ≠ 0 := fun h0 => hx (Fin.ext h0)
      simp [this]

end Count

include hlam hm in
/-- **The length of `W^{(ν)}`**: `p + p² + ⋯ + p^ν + p m`, i.e. `c(ν) + Σ_{i=1}^{ν} i(p−1)p^{ν−i}`
with `c(ν) = ν + p m`, `m = v_p(λ_ν)`. -/
theorem length_Wν_eq [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W)) (hlam0 : lam 0 = p) (hu : IsUnit u)
    (hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)}) :
    Module.length W (Wν W p ν) = ((∑ j ∈ Finset.range ν, p ^ (j + 1) + p * m : ℕ) : ℕ∞) := by
  rw [length_Wν hlam hm hW hlam0 hu hmax, ← Nat.cast_sum]
  congr 1
  have := sum_ord (Fact.out : p.Prime).pos ν (ν + p * m) (Nat.le_add_right _ _)
  rw [Finset.sum_range_succ'] at this
  simp only [pow_zero] at this
  omega

end ThetaBasis

section Standard

/-! ### The usual divided powers `λᵢ = p^{p^i}/(p^i)!` -/

variable (W : Type*) [CommRing W] [IsDomain W] [CharZero W] (p ν : ℕ) [Fact p.Prime]
  (hW : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : W))

omit [IsDomain W] [CharZero W] in
include hW in
/-- In `W`, `(p^i)! = p^{v_p((p^i)!)} · unit`. -/
theorem factorial_mul_unit (i : ℕ) :
    ∃ u : W, IsUnit u ∧ (((p ^ i)! : ℕ) : W) * u = (p : W) ^ padicValNat p (p ^ i)! := by
  have hp : p.Prime := Fact.out
  set n := (p ^ i)!
  have hn : n ≠ 0 := factorial_ne_zero _
  obtain ⟨U, hU⟩ := hW _ (Nat.not_dvd_ordCompl hp hn)
  refine ⟨↑U⁻¹, U⁻¹.isUnit, ?_⟩
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [Nat.cast_mul, Nat.cast_pow, ← hU, mul_assoc, Units.mul_inv, mul_one,
    Nat.factorization_def n hp]

include hW in
/-- **The usual divided powers of `p`** exist in `W`: `λᵢ (p^i)! = p^{p^i}`, so `λ₀ = p`,
`λᵢ^p = qᵢ λᵢ₊₁`, and `λᵢ = p^{p^i − v_p((p^i)!)} · unit`. -/
theorem exists_lamStd : ∃ lam : ℕ → W, lam 0 = p ∧ (∀ i, lam i ^ p = q p i * lam (i + 1)) ∧
    ∀ i, ∃ u : W, IsUnit u ∧ lam i = (p : W) ^ (p ^ i - padicValNat p (p ^ i)!) * u := by
  choose u hu hfac using factorial_mul_unit W p hW
  have hv : ∀ i, padicValNat p (p ^ i)! ≤ p ^ i := fun i => by
    have := sub_one_mul_padicValNat_factorial_pow p i
    have h2 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    have := Nat.le_mul_of_pos_left (padicValNat p (p ^ i)!) h2
    omega
  set lam : ℕ → W := fun i => (p : W) ^ (p ^ i - padicValNat p (p ^ i)!) * u i
  have hL : ∀ i, lam i * (((p ^ i)! : ℕ) : W) = (p : W) ^ (p ^ i) := fun i => by
    simp only [lam]
    rw [mul_assoc, mul_comm (u i), hfac, ← pow_add, Nat.sub_add_cancel (hv i)]
  have hF : ∀ i, (((p ^ i)! : ℕ) : W) ≠ 0 := fun i => Nat.cast_ne_zero.mpr (factorial_ne_zero _)
  refine ⟨lam, ?_, fun i => ?_, fun i => ⟨u i, hu i, rfl⟩⟩
  · have := hL 0
    rw [pow_zero, pow_one, factorial_one, Nat.cast_one, mul_one] at this
    exact this
  · apply mul_right_cancel₀ (pow_ne_zero p (hF i))
    have h1 := hL (i + 1)
    have h2 := congrArg (fun n : ℕ => (n : W)) (factorial_eq_mul_q p i)
    simp only [Nat.cast_mul, Nat.cast_pow] at h2
    rw [← mul_pow, hL, ← pow_mul, ← _root_.pow_succ, mul_assoc, mul_comm (lam (i + 1)),
      ← mul_assoc, mul_comm (q p i : W), ← h2, mul_comm, h1]

include hW in
/-- **The exact order of `1` in `W^{(ν)}` is `p^{c(ν)}`**, `c(ν) = ν + p(p^ν − v_p((p^ν)!))`
(page 5), when `p` is not a unit of `W` (`W(k)`, `ℤ_p`). -/
theorem p_pow_eq_zero_iff_std (hpu : ¬ IsUnit (p : W)) (k : ℕ) :
    (p : Wν W p ν) ^ k = 0 ↔ ν + p * (p ^ ν - padicValNat p (p ^ ν)!) ≤ k := by
  obtain ⟨lam, h0, hrec, hlam⟩ := exists_lamStd W p hW
  obtain ⟨u, hu, hm⟩ := hlam ν
  exact p_pow_eq_zero_iff hrec hm hW h0 hu hpu k

include hW in
/-- **The length of `W^{(ν)}`** over a discrete valuation ring with uniformiser `p`:
`p + p² + ⋯ + p^ν + p(p^ν − v_p((p^ν)!))`. -/
theorem length_Wν_std [IsDiscreteValuationRing W]
    (hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)}) :
    Module.length W (Wν W p ν) = ((∑ j ∈ Finset.range ν, p ^ (j + 1) +
      p * (p ^ ν - padicValNat p (p ^ ν)!) : ℕ) : ℕ∞) := by
  obtain ⟨lam, h0, hrec, hlam⟩ := exists_lamStd W p hW
  obtain ⟨u, hu, hm⟩ := hlam ν
  exact length_Wν_eq hrec hm hW h0 hu hmax

end Standard

/-- **For `W = ℤ_p`**: in `ℤ_p^{(ν)}`, `p^k = 0` iff `k ≥ c(ν) = ν + p(p^ν − v_p((p^ν)!))`, and
`ℤ_p^{(ν)}` has length `p + ⋯ + p^ν + p(p^ν − v_p((p^ν)!))`. -/
theorem padicInt_Wν (p ν : ℕ) [Fact p.Prime] :
    (∀ k, (p : Wν ℤ_[p] p ν) ^ k = 0 ↔ ν + p * (p ^ ν - padicValNat p (p ^ ν)!) ≤ k) ∧
      Module.length ℤ_[p] (Wν ℤ_[p] p ν) = ((∑ j ∈ Finset.range ν, p ^ (j + 1) +
        p * (p ^ ν - padicValNat p (p ^ ν)!) : ℕ) : ℕ∞) :=
  ⟨p_pow_eq_zero_iff_std ℤ_[p] p ν (padicInt_isUnit_natCast p) PadicInt.p_nonunit,
    length_Wν_std ℤ_[p] p ν (padicInt_isUnit_natCast p) PadicInt.maximalIdeal_eq_span_p⟩

end Grothendieck.Folder5
