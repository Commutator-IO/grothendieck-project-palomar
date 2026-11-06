module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot

@[expose] public section


/-!
# Folder 160, pages 7–9 and 13–15: the Moore determinant and the Dickson coefficients

The modernised reading `transcripts/160/160.modern.tex` defines, for a locally free `E` of
rank `n` with `u : E^{(p)} ⥲ E` (an étale `𝔽_p`-local system) and `ξ` a section of `Ě`,

> `Δₙ^E(ξ) = ξ ∧ ξ^{(p)} ∧ ⋯ ∧ ξ^{(p^{n-1})}`, soit une application polynomiale, homogène de
> degré `(pⁿ − 1)/(p − 1)`, `Δₙ^E : V(E) → V(ΛⁿE)`. … Sur [le complémentaire de son diviseur
> des zéros], `ξ, ξ^{(p)}, …, ξ^{(p^{n-1})}` forment une base de `Ě`, et l'on peut écrire
> `ξ^{(pⁿ)} + A^E_{n-1}(ξ) ξ^{(p^{n-1})} + ⋯ + A^E_0(ξ) ξ = 0`, ce qui définit des fonctions
> `A^E_i` uniquement déterminées. Comme dans le cas absolu, elles s'étendent à `V(E)` tout
> entier, … et l'on a encore `A^E_0 = (±1)(Δₙ^E)^{p-1}`.

This is finding `160-relative-moore-determinant`, in coordinates: `E` trivialised with `u` the
identity, so that `ξ ∈ Sⁿ` for an `𝔽_p`-algebra `S` and `ξ^{(p^i)} = (ξ_k^{p^i})_k`; the
Moore determinant is then `det(ξ_j^{p^i})` (pages 7–9, the absolute case).

* `moore_smul`, `moore_smul'`: `Δₙ(cξ) = c^{(pⁿ−1)/(p−1)} Δₙ(ξ)` over any commutative ring.
* `D_eq_C_mul_P`, `roots_D`: over `K = 𝔽_p[X₁, …, Xₙ]`,
  `D(T) = Δ_{n+1}(T, X₁, …, Xₙ) = (−1)ⁿ Δₙ · ∏_{λ ∈ 𝔽_pⁿ} (T − λ · X)`, with `Δₙ ≠ 0`
  (`Δ_ne_zero`, by induction through `D`): the factorisation the reading gives for the
  divisibility `Δ_i = A_i Δₙ` that page 9 asserts.
* `dickson_relation`: the `A_i ∈ 𝔽_p[X]` (coefficients of `∏ (T − λ · X)`) satisfy
  `X_k^{pⁿ} + Σ A_i X_k^{p^i} = 0`; `A_zero`: `A₀ = (−1)ⁿ Δₙ^{p−1}`.
* `dickson_relation_eval`, `dickson_unique`, `A_zero_eval`: for every `𝔽_p`-algebra `S` and
  `ξ ∈ Sⁿ` the relation holds with the `A_i(ξ)`, and where `Δₙ(ξ)` is invertible they are its
  only coefficients: the `A_i^E` extend from the complement of the zero divisor of `Δₙ` to
  all of `V(E)`, and `A₀ = (−1)ⁿ Δₙ^{p−1}` everywhere.

* `corollaire_page13_faux` (finding `160-special-linear-structures-sign`): the Corollary of
  page 13, trivialisations of `ΛⁿM` « ↔ » `(p − 1)`-th roots of `a₀`, fails for `p` and `n`
  odd: over `𝔽₃`, `M = 𝔽₃ = Ker(x³ − x)`, `a₀ = −1` has no square root while `Λ¹M` has two
  trivialisations.
* `moore_act`, `moore_pow_sub_one`, `moore_act_surj`, `moore_act_eq_iff`: the corrected form
  over a field `K` of characteristic `p`: `Δₙ(g · e) = det g · Δₙ(e)` for `g` over `𝔽_p`,
  `Δₙ(e)` is a `(p − 1)`-th root of `(−1)ⁿ a₀`, every such root is a `Δₙ(g · e)`, and
  `Δₙ(g · e) = Δₙ(h · e)` iff `det g = det h`: the trivialisations correspond to the roots of
  `(−1)ⁿ a₀`, with fibres the `SLₙ(𝔽_p)`-orbits.

**What the formalisation finds.** The statement holds in coordinates, with the sign `(−1)ⁿ`
that page and reading leave as `±`. The extension rests on the factorisation of `D(T)`, which
needs only that the `p^n` forms `λ · X` are distinct roots of a polynomial of degree `pⁿ` with
leading coefficient `±Δₙ ≠ 0`; the factorisation of page 7 with its constant `c` is not
needed. Not formalised: the relative version for a non-trivial `(E, u)` (the reduction to the
trivial local system is étale-local), the trivialisation `(ΛⁿĚ)^{⊗(p−1)} ≅ 𝒪_S` by `Λⁿǔ`,
and Dickson's theorem (pages 9–12).
-/

open Matrix Polynomial

namespace Grothendieck.Folder160

variable {R : Type*} [CommRing R] (p : ℕ)

/-- The Moore matrix `(ξ_j^{p^i})`. -/
def mooreMat {n : ℕ} (ξ : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j => ξ j ^ p ^ (i : ℕ)

/-- The Moore determinant `Δₙ(ξ) = det(ξ_j^{p^i})`. -/
def moore {n : ℕ} (ξ : Fin n → R) : R := (mooreMat p ξ).det

/-- `Δₙ(cξ) = c^{1 + p + ⋯ + p^{n-1}} Δₙ(ξ)`, over any commutative ring. -/
theorem moore_smul {n : ℕ} (c : R) (ξ : Fin n → R) :
    moore p (c • ξ) = c ^ (∑ i ∈ Finset.range n, p ^ i) * moore p ξ := by
  have : mooreMat p (c • ξ) = of fun (i j : Fin n) => c ^ p ^ (i : ℕ) * mooreMat p ξ i j := by
    ext i j; simp [mooreMat, mul_pow]
  rw [moore, this, det_mul_column, ← Finset.prod_pow_eq_pow_sum, ← Fin.prod_univ_eq_prod_range]
  rfl

/-- **Homogeneity of degree `(pⁿ − 1)/(p − 1)`.** -/
theorem moore_smul' (hp : 2 ≤ p) {n : ℕ} (c : R) (ξ : Fin n → R) :
    moore p (c • ξ) = c ^ ((p ^ n - 1) / (p - 1)) * moore p ξ := by
  rw [moore_smul, Nat.geomSum_eq hp]

theorem map_moore {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ} (ξ : Fin n → R) :
    f (moore p ξ) = moore p (f ∘ ξ) := by
  rw [moore, RingHom.map_det]
  congr 1
  ext i j; simp [mooreMat]

/-! ### The universal case: Moore determinants over `𝔽_p[X₁, …, Xₙ]` -/

variable [hp : Fact p.Prime]

/-- `Δₙ(X₁, …, Xₙ) ∈ 𝔽_p[X₁, …, Xₙ]`. -/
noncomputable def Δ (n : ℕ) : MvPolynomial (Fin n) (ZMod p) := moore p MvPolynomial.X

/-- `D(T) = Δ_{n+1}(T, X₁, …, Xₙ)`, a polynomial in `T` over `𝔽_p[X₁, …, Xₙ]`. -/
noncomputable def D (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  moore p (Fin.cons Polynomial.X fun k => Polynomial.C (MvPolynomial.X k))

/-- The minors of the expansion of `D` along its first column. -/
noncomputable def minor (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) (ZMod p) :=
  (of fun (r : Fin n) (k : Fin n) => (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod p)) ^
    p ^ ((i.succAbove r : Fin (n + 1)) : ℕ)).det

theorem D_eq (n : ℕ) : D p n = ∑ i : Fin (n + 1),
    Polynomial.C ((-1) ^ (i : ℕ) * minor p n i) * Polynomial.X ^ p ^ (i : ℕ) := by
  rw [D, moore, det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsub : (mooreMat p (Fin.cons (Polynomial.X : (MvPolynomial (Fin n) (ZMod p))[X])
      fun k => Polynomial.C (MvPolynomial.X k))).submatrix i.succAbove Fin.succ =
      (Polynomial.C : MvPolynomial (Fin n) (ZMod p) →+* _).mapMatrix
        (of fun (r : Fin n) (k : Fin n) => (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod p)) ^
          p ^ ((i.succAbove r : Fin (n + 1)) : ℕ)) := by
    ext r k; simp [mooreMat]
  rw [hsub, ← RingHom.map_det, minor]
  simp only [mooreMat, of_apply, Fin.cons_zero, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_1]
  ring

theorem pow_injective : Function.Injective fun i : ℕ => p ^ i :=
  Nat.pow_right_injective hp.out.two_le

theorem coeff_D (n : ℕ) (i : Fin (n + 1)) :
    (D p n).coeff (p ^ (i : ℕ)) = (-1) ^ (i : ℕ) * minor p n i := by
  rw [D_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    intro h
    exact hj (Fin.ext (pow_injective p h).symm)
  · simp

theorem coeff_D_of_ne (n : ℕ) (m : ℕ) (hm : ∀ i : Fin (n + 1), m ≠ p ^ (i : ℕ)) :
    (D p n).coeff m = 0 := by
  rw [D_eq, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (hm i)

theorem minor_last (n : ℕ) : minor p n (Fin.last n) = Δ p n := by
  simp only [minor, Fin.succAbove_last, Fin.val_castSucc]
  rfl

theorem minor_zero (n : ℕ) : minor p n 0 = Δ p n ^ p := by
  rw [Δ, moore, ← frobenius_def (R := MvPolynomial (Fin n) (ZMod p)) p, RingHom.map_det, minor]
  congr 1
  ext r k
  simp [mooreMat, pow_succ, pow_mul, frobenius_def]

theorem natDegree_D_le (n : ℕ) : (D p n).natDegree ≤ p ^ n := by
  rw [D_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.pow_le_pow_right hp.out.pos (Nat.lt_succ_iff.1 i.2)

theorem finSuccEquiv_Δ (n : ℕ) :
    MvPolynomial.finSuccEquiv (ZMod p) n (Δ p (n + 1)) = D p n := by
  rw [Δ, D]
  have := map_moore p (MvPolynomial.finSuccEquiv (ZMod p) n).toRingEquiv.toRingHom
    (MvPolynomial.X : Fin (n + 1) → _)
  simp only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ]

/-- `Δₙ ≠ 0` in `𝔽_p[X₁, …, Xₙ]`. -/
theorem Δ_ne_zero (n : ℕ) : Δ p n ≠ 0 := by
  induction n with
  | zero => simp [Δ, moore]
  | succ n ih =>
    intro h
    have h1 := congrArg (MvPolynomial.finSuccEquiv (ZMod p) n) h
    rw [finSuccEquiv_Δ, map_zero] at h1
    have := coeff_D p n (Fin.last n)
    rw [h1, Polynomial.coeff_zero, minor_last] at this
    exact ih (by simpa using this.symm)

/-- The linear form `λ · X = Σ λ_k X_k`. -/
noncomputable def lin {n : ℕ} (l : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ k, MvPolynomial.C (l k) * MvPolynomial.X k

theorem lin_injective (n : ℕ) : Function.Injective (lin p (n := n)) := by
  intro l l' h
  ext k
  have := congrArg (MvPolynomial.eval (Pi.single k 1)) h
  simpa [lin, Pi.single_apply] using this

theorem natDegree_D (n : ℕ) : (D p n).natDegree = p ^ n := by
  refine le_antisymm (natDegree_D_le p n) (Polynomial.le_natDegree_of_ne_zero ?_)
  have := coeff_D p n (Fin.last n)
  simp only [Fin.val_last] at this
  rw [this, minor_last]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Δ_ne_zero p n)

theorem leadingCoeff_D (n : ℕ) : (D p n).leadingCoeff = (-1) ^ n * Δ p n := by
  rw [Polynomial.leadingCoeff, natDegree_D]
  have := coeff_D p n (Fin.last n)
  simp only [Fin.val_last] at this
  rw [this, minor_last]

/-- Each `λ · X` is a root of `D`: the first column becomes a combination of the others. -/
theorem D_eval_lin {n : ℕ} (l : Fin n → ZMod p) : (D p n).eval (lin p l) = 0 := by
  rw [D, ← Polynomial.coe_evalRingHom, map_moore]
  rw [moore, ← exists_mulVec_eq_zero_iff]
  refine ⟨Fin.cons (-1) fun k => MvPolynomial.C (l k), fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp at this
  · ext i
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, mooreMat, of_apply, Function.comp_apply,
      Fin.cons_zero, Fin.cons_succ, Polynomial.coe_evalRingHom, Polynomial.eval_X,
      Polynomial.eval_C, Pi.zero_apply]
    rw [lin, sum_pow_char_pow]
    simp only [mul_pow, ← map_pow, ZMod.pow_card_pow]
    simp [mul_comm]

/-- The roots of `D` are the `p^n` forms `λ · X`. -/
theorem roots_D (n : ℕ) :
    (D p n).roots = (Finset.univ.image (lin p (n := n))).val := by
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset (Finset.nodup _)]
    intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Polynomial.mem_roots]
    · exact D_eval_lin p l
    · intro h
      have := natDegree_D p n
      rw [h, Polynomial.natDegree_zero] at this
      exact pow_ne_zero _ hp.out.ne_zero this.symm
  · rw [Finset.card_val, Finset.card_image_of_injective _ (lin_injective p n)]
    simp only [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact (Polynomial.card_roots' _).trans (natDegree_D p n).le

/-- `P(T) = ∏_{λ ∈ 𝔽_p^n} (T − λ · X) = D(T)/((−1)ⁿ Δₙ)`. -/
noncomputable def P (n : ℕ) : (MvPolynomial (Fin n) (ZMod p))[X] :=
  ((D p n).roots.map fun a => Polynomial.X - Polynomial.C a).prod

theorem card_roots_D (n : ℕ) : Multiset.card (D p n).roots = (D p n).natDegree := by
  rw [roots_D, natDegree_D, Finset.card_val, Finset.card_image_of_injective _ (lin_injective p n)]
  simp

theorem D_eq_C_mul_P (n : ℕ) : D p n = Polynomial.C ((-1) ^ n * Δ p n) * P p n := by
  rw [← leadingCoeff_D, P, Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_D p n)]

theorem P_monic (n : ℕ) : (P p n).Monic :=
  Polynomial.monic_multiset_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a

theorem natDegree_P (n : ℕ) : (P p n).natDegree = p ^ n := by
  rw [P, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, card_roots_D, natDegree_D]

theorem lc_ne_zero (n : ℕ) : ((-1) ^ n * Δ p n : MvPolynomial (Fin n) (ZMod p)) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Δ_ne_zero p n)

/-- The Dickson coefficients `A_i`, polynomials in `X₁, …, Xₙ`. -/
noncomputable def A (n i : ℕ) : MvPolynomial (Fin n) (ZMod p) := (P p n).coeff (p ^ i)

theorem coeff_P_of_ne (n m : ℕ) (hm : ∀ i : Fin (n + 1), m ≠ p ^ (i : ℕ)) :
    (P p n).coeff m = 0 := by
  have h := coeff_D_of_ne p n m hm
  rw [D_eq_C_mul_P, Polynomial.coeff_C_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (lc_ne_zero p n)

theorem lc_mul_A (n : ℕ) (i : Fin (n + 1)) :
    (-1) ^ n * Δ p n * A p n i = (-1) ^ (i : ℕ) * minor p n i := by
  rw [A, ← Polynomial.coeff_C_mul, ← D_eq_C_mul_P, coeff_D]

theorem A_top (n : ℕ) : A p n n = 1 := by
  rw [A, ← natDegree_P]; exact P_monic p n

theorem eval_P {n : ℕ} (x : MvPolynomial (Fin n) (ZMod p)) :
    (P p n).eval x = ∑ i : Fin (n + 1), A p n i * x ^ p ^ (i : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (n := p ^ n + 1) (by rw [natDegree_P]; omega)]
  have hsub : Finset.univ.image (fun i : Fin (n + 1) => p ^ (i : ℕ)) ⊆
      Finset.range (p ^ n + 1) := by
    intro m hm
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hm
    exact Finset.mem_range.2 (Nat.lt_succ_of_le
      (Nat.pow_le_pow_right hp.out.pos (Nat.lt_succ_iff.1 i.2)))
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · rfl
  · intro i _ j _ h; exact Fin.ext (pow_injective p h)
  · intro m _ hm
    rw [coeff_P_of_ne p n m fun i h => hm (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h.symm⟩),
      zero_mul]

theorem lin_single {n : ℕ} (k : Fin n) : lin p (Pi.single k 1) = MvPolynomial.X k := by
  simp [lin, Pi.single_apply]

/-- **The Dickson relation**: `X_k^{pⁿ} + A_{n-1} X_k^{p^{n-1}} + ⋯ + A₀ X_k = 0`. -/
theorem dickson_relation {n : ℕ} (k : Fin n) :
    (MvPolynomial.X k : MvPolynomial (Fin n) (ZMod p)) ^ p ^ n +
      ∑ i : Fin n, A p n i * MvPolynomial.X k ^ p ^ (i : ℕ) = 0 := by
  have h := D_eval_lin p (Pi.single k 1)
  rw [D_eq_C_mul_P, Polynomial.eval_mul, Polynomial.eval_C, lin_single] at h
  have h' := (mul_eq_zero.1 h).resolve_left (lc_ne_zero p n)
  rw [eval_P, Fin.sum_univ_castSucc] at h'
  simp only [Fin.val_castSucc, Fin.val_last, A_top, one_mul] at h'
  rw [add_comm]; exact h'

/-- **`A₀ = (−1)ⁿ Δₙ^{p−1}`.** -/
theorem A_zero (n : ℕ) : A p n 0 = (-1) ^ n * Δ p n ^ (p - 1) := by
  have h := lc_mul_A p n 0
  simp only [Fin.val_zero, pow_zero, one_mul, minor_zero] at h
  have hp1 : Δ p n ^ p = Δ p n ^ (p - 1) * Δ p n := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  apply mul_left_cancel₀ (lc_ne_zero p n)
  rw [h, hp1]
  rw [show (-1 : MvPolynomial (Fin n) (ZMod p)) ^ n * Δ p n * ((-1) ^ n * Δ p n ^ (p - 1)) =
    ((-1) ^ n * (-1) ^ n) * (Δ p n ^ (p - 1) * Δ p n) by ring, ← mul_pow]
  simp

/-! ### Over an `𝔽_p`-algebra, `E` trivialised -/

variable {S : Type*} [CommRing S] [Algebra (ZMod p) S]

/-- The `A_i(ξ)` are defined for every `ξ ∈ V(E)`, not only where `Δₙ(ξ)` is invertible: the
Dickson relation holds at every point. -/
theorem dickson_relation_eval {n : ℕ} (ξ : Fin n → S) (k : Fin n) :
    ξ k ^ p ^ n + ∑ i : Fin n, MvPolynomial.aeval ξ (A p n i) * ξ k ^ p ^ (i : ℕ) = 0 := by
  simpa using congrArg (MvPolynomial.aeval ξ) (dickson_relation p k)

/-- **Where `Δₙ(ξ)` is invertible, the coefficients of the relation are unique, and are the
values of the polynomials `A_i`**: the `A_i^E` of the complement of the zero divisor of `Δₙ`
extend to all of `V(E)`. -/
theorem dickson_unique {n : ℕ} (ξ : Fin n → S) (hξ : IsUnit (moore p ξ)) (a : Fin n → S)
    (ha : ∀ k, ξ k ^ p ^ n + ∑ i : Fin n, a i * ξ k ^ p ^ (i : ℕ) = 0) :
    a = fun i : Fin n => MvPolynomial.aeval ξ (A p n i) := by
  set v : Fin n → S := fun i => a i - MvPolynomial.aeval ξ (A p n i)
  have hv : v ᵥ* mooreMat p ξ = 0 := by
    ext k
    have h1 := ha k
    have h2 := dickson_relation_eval p ξ k
    simp only [vecMul, dotProduct, mooreMat, of_apply, v, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    linear_combination h1 - h2
  have : v = 0 := by
    rw [← vecMul_one v, ← mul_nonsing_inv (mooreMat p ξ) hξ, ← vecMul_vecMul, hv, zero_vecMul]
  funext i
  exact sub_eq_zero.1 (congrFun this i)

theorem A_zero_eval {n : ℕ} (ξ : Fin n → S) :
    MvPolynomial.aeval ξ (A p n 0) = (-1) ^ n * moore p ξ ^ (p - 1) := by
  rw [A_zero, map_mul, map_pow, map_pow, map_neg, map_one, Δ]
  congr 2
  have := map_moore p (MvPolynomial.aeval (R := ZMod p) ξ).toRingHom
    (MvPolynomial.X : Fin n → MvPolynomial (Fin n) (ZMod p))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]; congr 1; ext k; simp

/-! ### Page 13: the sign in the Corollary -/

/-- **The Corollary of page 13 fails as stated.** Over `𝔽₃`, with `n = 1` and `M = 𝔽₃`, the
kernel of `x³ − x`, one has `a₀ = A₀(1) = −1`, which has no square root in `𝔽₃`, while
`Λ¹M = M` has two trivialisations (its two nonzero elements). -/
theorem corollaire_page13_faux :
    MvPolynomial.aeval (fun _ : Fin 1 => (1 : ZMod 3)) (A 3 1 0) = -1 ∧
      (¬ ∃ y : ZMod 3, y ^ (3 - 1) = -1) ∧ Fintype.card {t : ZMod 3 // t ≠ 0} = 2 := by
  refine ⟨?_, by decide, by decide⟩
  rw [A_zero_eval]
  simp [moore, mooreMat, det_unique]

/-- `g · e`, with `(g · e)_j = Σ_k g_{jk} e_k`, for a matrix `g` over `𝔽_p`. -/
def act {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) (e : Fin n → S) : Fin n → S :=
  fun j => ∑ k, algebraMap (ZMod p) S (g j k) * e k

/-- **`Δₙ(g · e) = det g · Δₙ(e)`**: the coefficients of `g` are fixed by the Frobenius, so the
Moore matrix of `g · e` is that of `e` times `gᵀ`. -/
theorem moore_act [CharP S p] {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) (e : Fin n → S) :
    moore p (act p g e) = algebraMap (ZMod p) S g.det * moore p e := by
  have h : mooreMat p (act p g e) = mooreMat p e * (g.map (algebraMap (ZMod p) S))ᵀ := by
    ext i j
    simp only [mooreMat, act, of_apply, mul_apply, transpose_apply, map_apply]
    rw [sum_pow_char_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← map_pow, ZMod.pow_card_pow, mul_comm]
  rw [moore, h, det_mul, det_transpose, RingHom.map_det, RingHom.mapMatrix_apply, mul_comm, moore]

/-- `Δₙ(e)` is a `(p − 1)`-th root of `(−1)ⁿ a₀`, `a₀ = A₀(e)`. -/
theorem moore_pow_sub_one {n : ℕ} (e : Fin n → S) :
    moore p e ^ (p - 1) = (-1) ^ n * MvPolynomial.aeval e (A p n 0) := by
  rw [A_zero_eval, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/-- In a field of characteristic `p`, the solutions of `c^p = c` are the elements of `𝔽_p`. -/
theorem eq_algebraMap_of_pow_eq (c : K) (hc : c ^ p = c) :
    ∃ a : ZMod p, algebraMap (ZMod p) K a = c := by
  classical
  by_contra h
  simp only [not_exists] at h
  have hQ : (X ^ p - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.out.one_lt
  have hroot : ∀ x : K, x ^ p = x → x ∈ (X ^ p - X : K[X]).roots := fun x hx => by
    rw [mem_roots hQ, IsRoot.def, eval_sub, eval_pow, eval_X, hx, sub_self]
  set s : Finset K := insert c (Finset.univ.image (algebraMap (ZMod p) K))
  have hs : s.val ≤ (X ^ p - X : K[X]).roots := by
    rw [Multiset.le_iff_subset s.nodup]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hroot _ hc
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have hcard : s.card = p + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h]),
      Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective, Finset.card_univ,
      ZMod.card]
  have := (Multiset.card_le_card hs).trans (card_roots' _)
  rw [Finset.card_val, hcard, FiniteField.X_pow_card_sub_X_natDegree_eq K hp.out.one_lt] at this
  omega

/-- **The corrected Corollary, over a field.** For `e ∈ Kⁿ` with `Δₙ(e) ≠ 0` (a basis of an
`n`-dimensional `𝔽_p`-subspace `M ⊂ K`), every `(p − 1)`-th root of `(−1)ⁿ a₀` is `Δₙ(g · e)`
for some `g ∈ GLₙ(𝔽_p)`. -/
theorem moore_act_surj {n : ℕ} (hn : 0 < n) (e : Fin n → K) (he : moore p e ≠ 0) (y : K)
    (hy : y ^ (p - 1) = (-1) ^ n * MvPolynomial.aeval e (A p n 0)) :
    ∃ g : Matrix (Fin n) (Fin n) (ZMod p), IsUnit g.det ∧ moore p (act p g e) = y := by
  have := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  rw [← moore_pow_sub_one] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hp1] at hy
    exact he ((pow_eq_zero_iff hp1).1 hy.symm)
  set c := y / moore p e with hcdef
  have hc1 : c ^ (p - 1) = 1 := by rw [div_pow, hy, div_self (pow_ne_zero _ he)]
  have hc : c ^ p = c := by
    rw [← Nat.sub_add_cancel hp.out.one_le, pow_succ, hc1, one_mul]
  obtain ⟨a, ha⟩ := eq_algebraMap_of_pow_eq p c hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact div_ne_zero hy0 he ha.symm
  have hdet : (diagonal (Function.update 1 (⟨0, hn⟩ : Fin n) a)).det = a := by
    rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨diagonal (Function.update 1 (⟨0, hn⟩ : Fin n) a), by rw [hdet]; exact ha0.isUnit, ?_⟩
  rw [moore_act, hdet, ha, hcdef, div_mul_cancel₀ _ he]

/-- **The fibres are the `SLₙ(𝔽_p)`-orbits**: `Δₙ(g · e) = Δₙ(h · e)` iff `det g = det h`. -/
theorem moore_act_eq_iff {n : ℕ} (e : Fin n → K) (he : moore p e ≠ 0)
    (g h : Matrix (Fin n) (Fin n) (ZMod p)) :
    moore p (act p g e) = moore p (act p h e) ↔ g.det = h.det := by
  have := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  rw [moore_act, moore_act, mul_left_inj' he, (algebraMap (ZMod p) K).injective.eq_iff]


/-! ### Two bases of the same `M` differ by an element of `GLₙ(𝔽_p)` -/

/-- **Two bases of the same `M` differ by an element of `GLₙ(𝔽_p)`.** If `e, f ∈ Kⁿ` are
`𝔽_p`-linearly independent and span the same `𝔽_p`-subspace `M ⊂ K`, then `f = g · e` for a
matrix `g` over `𝔽_p` with invertible determinant: `g` is the transpose of the change-of-basis
matrix `Basis.toMatrix`, invertible by `Basis.invertibleToMatrix`. -/
theorem exists_act_eq_of_span_eq {n : ℕ} {e f : Fin n → K}
    (he : LinearIndependent (ZMod p) e) (hf : LinearIndependent (ZMod p) f)
    (hM : Submodule.span (ZMod p) (Set.range e) = Submodule.span (ZMod p) (Set.range f)) :
    ∃ g : Matrix (Fin n) (Fin n) (ZMod p), IsUnit g.det ∧ act p g e = f := by
  let be : Module.Basis (Fin n) (ZMod p) (Submodule.span (ZMod p) (Set.range e)) :=
    Module.Basis.span he
  let bf : Module.Basis (Fin n) (ZMod p) (Submodule.span (ZMod p) (Set.range e)) :=
    (Module.Basis.span hf).map (LinearEquiv.ofEq _ _ hM.symm)
  have := be.invertibleToMatrix bf
  refine ⟨(be.toMatrix bf)ᵀ, by rw [det_transpose]; exact isUnit_det_of_invertible _, ?_⟩
  funext j
  have h := congrArg Subtype.val (be.sum_toMatrix_smul_self bf j)
  have hbf : ((bf j : Submodule.span (ZMod p) (Set.range e)) : K) = f j := by
    simp [bf, Module.Basis.span_apply]
  simpa [act, Algebra.smul_def, be, hbf, Module.Basis.span_apply] using h

/-- **The Moore determinants of two bases of `M` differ by `det g`, `g ∈ GLₙ(𝔽_p)`**: every
trivialisation `Δₙ(f)` given by a basis `f` of `M` is a `Δₙ(g · e)` for one fixed basis `e`. -/
theorem moore_eq_of_span_eq {n : ℕ} {e f : Fin n → K}
    (he : LinearIndependent (ZMod p) e) (hf : LinearIndependent (ZMod p) f)
    (hM : Submodule.span (ZMod p) (Set.range e) = Submodule.span (ZMod p) (Set.range f)) :
    ∃ g : Matrix (Fin n) (Fin n) (ZMod p), IsUnit g.det ∧ act p g e = f ∧
      moore p f = algebraMap (ZMod p) K g.det * moore p e := by
  have := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  obtain ⟨g, hg, rfl⟩ := exists_act_eq_of_span_eq p he hf hM
  exact ⟨g, hg, rfl, moore_act p g e⟩


/-! ### Dickson's theorem (pages 9–12)

`𝔽_p[X₁, …, Xₙ]^{GLₙ(𝔽_p)} = 𝔽_p[A₀, …, A_{n−1}]` (`dickson_theorem`) and
`𝔽_p[X₁, …, Xₙ]^{SLₙ(𝔽_p)} = 𝔽_p[Δₙ, A₁, …, A_{n−1}]` (`dickson_theorem_SL`), both polynomial
algebras (`dickson_algebraicIndependent`, `dicksonSL_algebraicIndependent`). The proof is the
Galois one, not the page's (Zariski's Main Theorem): `𝔽_p[X]` is integral over `𝔽_p[A]`, since
each `X_k` is a root of the monic `∏ (T − λ · X)`, so the `n` elements `A_i` are algebraically
independent (transcendence degree); `𝔽_p(X)` is the splitting field over `𝔽_p(A)` of
`∏ (T − λ · X)`, separable since its derivative is `A₀ ≠ 0`, and each of its automorphisms sends
`X_k` to some `λ · X`, so is some `g ∈ GLₙ(𝔽_p)`; an invariant thus lies in `𝔽_p(A)`, and in
`𝔽_p[A]` since a polynomial algebra is integrally closed. -/

/-- The Dickson invariants `A₀, …, A_{n−1}`. -/
noncomputable def dickson (n : ℕ) (i : Fin n) : MvPolynomial (Fin n) (ZMod p) := A p n i

theorem P_eval_lin {n : ℕ} (l : Fin n → ZMod p) : (P p n).eval (lin p l) = 0 := by
  have h := D_eval_lin p l
  rw [D_eq_C_mul_P, eval_mul, eval_C] at h
  exact (mul_eq_zero.1 h).resolve_left (lc_ne_zero p n)

theorem coeff_P_mem (n m : ℕ) :
    (P p n).coeff m ∈ Algebra.adjoin (ZMod p) (Set.range (dickson p n)) := by
  by_cases hm : ∃ i : Fin (n + 1), m = p ^ (i : ℕ)
  · obtain ⟨i, rfl⟩ := hm
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
    · rw [Fin.val_last, ← A, A_top]; exact one_mem _
  · rw [coeff_P_of_ne p n m fun i h => hm ⟨i, h⟩]; exact zero_mem _

/-- For every `ξ ∈ Tⁿ`, each `f(ξ)` is integral over any subalgebra containing the `A_i(ξ)`. -/
theorem isIntegral_aeval {n : ℕ} {T : Type*} [CommRing T] [Algebra (ZMod p) T] (ξ : Fin n → T)
    (B : Subalgebra (ZMod p) T) (hB : ∀ i, MvPolynomial.aeval ξ (dickson p n i) ∈ B)
    (f : MvPolynomial (Fin n) (ZMod p)) : IsIntegral B (MvPolynomial.aeval ξ f) := by
  have hX : ∀ k, IsIntegral B (ξ k) := fun k => by
    have hl : (P p n).map (MvPolynomial.aeval ξ).toRingHom ∈ lifts (algebraMap B T) :=
      (lifts_iff_coeff_lifts _).2 fun m => by
        have h := (Subalgebra.mem_map (f := MvPolynomial.aeval ξ)).2 ⟨_, coeff_P_mem p n m, rfl⟩
        rw [AlgHom.map_adjoin, ← Set.range_comp] at h
        exact ⟨⟨_, Algebra.adjoin_le (Set.range_subset_iff.2 hB) h⟩, by rw [coeff_map]; rfl⟩
    obtain ⟨q, hq, -, hmo⟩ := lifts_and_natDegree_eq_and_monic hl ((P_monic p n).map _)
    refine ⟨q, hmo, ?_⟩
    rw [← eval_map, hq, eval_map, ← MvPolynomial.aeval_X (R := ZMod p) ξ k,
      show MvPolynomial.aeval ξ (MvPolynomial.X k) = (MvPolynomial.aeval ξ).toRingHom
        (MvPolynomial.X k) from rfl, eval₂_at_apply, ← lin_single, P_eval_lin, map_zero]
  induction f using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply (ZMod p) B T]
           exact isIntegral_algebraMap
  | add f g hf hg => rw [map_add]; exact hf.add hg
  | mul_X f k hf => rw [map_mul, MvPolynomial.aeval_X]; exact hf.mul (hX k)

theorem P_eq_prod (n : ℕ) : P p n = ∏ l : Fin n → ZMod p, (X - C (lin p l)) := by
  rw [P, roots_D, ← Finset.prod_eq_multiset_prod, Finset.prod_image fun l _ l' _ h =>
    lin_injective p n h]

theorem aeval_act_lin {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) (l : Fin n → ZMod p) :
    MvPolynomial.aeval (act p g MvPolynomial.X) (lin p l) = lin p (l ᵥ* g) := by
  simp only [lin, act, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, vecMul,
    dotProduct, MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  rw [Finset.sum_comm]

/-- **The Dickson invariants are invariant under `GLₙ(𝔽_p)`**: `g` permutes the forms `λ · X`. -/
theorem aeval_act_dickson {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) (hg : IsUnit g.det)
    (i : Fin n) : MvPolynomial.aeval (act p g MvPolynomial.X) (dickson p n i) = dickson p n i := by
  have hbij : Function.Bijective fun l : Fin n → ZMod p => l ᵥ* g :=
    Finite.injective_iff_bijective.1 fun l l' h => by
      simpa [vecMul_vecMul, mul_nonsing_inv _ hg] using congrArg (· ᵥ* g⁻¹) h
  have h : (P p n).map (MvPolynomial.aeval (act p g MvPolynomial.X)).toRingHom = P p n := by
    rw [P_eq_prod, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_act_lin]
    exact Fintype.prod_bijective _ hbij _ _ fun _ => rfl
  rw [dickson, A]; conv_rhs => rw [← h]
  rw [coeff_map]; rfl

/-- A family `x` whose subalgebra contains the `A_i` is algebraically independent:
`𝔽_p[X₁, …, Xₙ]` is integral over `𝔽_p[x]`, so the `n` elements `x_i` span a ring of
transcendence degree `n`. -/
theorem algebraicIndependent_of {n : ℕ} (x : Fin n → MvPolynomial (Fin n) (ZMod p))
    (hx : ∀ i, dickson p n i ∈ Algebra.adjoin (ZMod p) (Set.range x)) :
    AlgebraicIndependent (ZMod p) x := by
  have : Algebra.IsIntegral (Algebra.adjoin (ZMod p) (Set.range x))
      (MvPolynomial (Fin n) (ZMod p)) :=
    ⟨fun f => by
      have := isIntegral_aeval p MvPolynomial.X _
        (fun i => by rw [MvPolynomial.aeval_X_left_apply]; exact hx i) f
      rwa [MvPolynomial.aeval_X_left_apply] at this⟩
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite (ZMod p) x
    (by rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id])).1

/-- **The Dickson invariants are algebraically independent**: `𝔽_p[A₀, …, A_{n−1}]` is a
polynomial algebra on them. -/
theorem dickson_algebraicIndependent (n : ℕ) : AlgebraicIndependent (ZMod p) (dickson p n) :=
  algebraicIndependent_of p _ fun i => Algebra.subset_adjoin ⟨i, rfl⟩

/-! #### The Galois argument, in `𝔽_p(X₁, …, Xₙ)` -/

local notation "𝕂" n:max => FractionRing (MvPolynomial (Fin n) (ZMod p))
local notation "ι" n:max => algebraMap (MvPolynomial (Fin n) (ZMod p)) (𝕂 n)

theorem roots_map_P (n : ℕ) :
    ((P p n).map (ι n)).roots =
      (Finset.univ.image (lin p (n := n))).val.map (ι n) := by
  have hr : (P p n).roots = (D p n).roots := roots_multiset_prod_X_sub_C _
  rw [← roots_D, ← hr, roots_map_of_injective_of_card_eq_natDegree (IsFractionRing.injective _ _)]
  rw [hr, card_roots_D, natDegree_D, natDegree_P]

theorem derivative_P (n : ℕ) : derivative (P p n) = C (A p n 0) := by
  ext m
  rw [coeff_derivative, coeff_C]
  split_ifs with hm
  · subst hm; simp [A]
  · by_cases h : ∃ i : Fin (n + 1), m + 1 = p ^ (i : ℕ)
    · obtain ⟨i, hi⟩ := h
      have hi0 : (i : ℕ) ≠ 0 := by rintro h0; rw [h0, pow_zero] at hi; omega
      have : ((m : MvPolynomial (Fin n) (ZMod p)) + 1) = ((p ^ (i : ℕ) : ℕ) : _) := by
        rw [← hi]; push_cast; rfl
      rw [this, (CharP.cast_eq_zero_iff _ p _).2 (dvd_pow_self p hi0), mul_zero]
    · rw [coeff_P_of_ne p n _ fun i h' => h ⟨i, h'⟩, zero_mul]

section
variable {n : ℕ} (x : Fin n → MvPolynomial (Fin n) (ZMod p))
  (hx : ∀ i, dickson p n i ∈ Algebra.adjoin (ZMod p) (Set.range x))
include hx

/-- The field `𝔽_p(x) ⊂ 𝔽_p(X₁, …, Xₙ)` generated by the family `x`. -/
noncomputable abbrev field : IntermediateField (ZMod p) (𝕂 n) :=
  IntermediateField.adjoin (ZMod p) (Set.range ((ι n) ∘ x))

omit hx in
theorem map_adjoin_eq :
    (Algebra.adjoin (ZMod p) (Set.range x)).map (IsScalarTower.toAlgHom (ZMod p) _ (𝕂 n)) =
      Algebra.adjoin (ZMod p) (Set.range ((ι n) ∘ x)) := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]; rfl

theorem exists_map_eq_P : ∃ Q : (field p x)[X],
    Q.map (algebraMap _ (𝕂 n)) = (P p n).map (ι n) :=
  (lifts_iff_coeff_lifts _).2 fun m => by
    have h := (Subalgebra.mem_map (f := IsScalarTower.toAlgHom (ZMod p) _ (𝕂 n))).2
      ⟨_, Algebra.adjoin_le (Set.range_subset_iff.2 hx) (coeff_P_mem p n m), rfl⟩
    rw [map_adjoin_eq] at h
    exact ⟨⟨_, IntermediateField.algebra_adjoin_le_adjoin _ _ h⟩, by rw [coeff_map]; rfl⟩

omit hx in
theorem eval_map_P_X (k : Fin n) :
    ((P p n).map (ι n)).eval ((ι n) (MvPolynomial.X k)) = 0 := by
  rw [eval_map, eval₂_at_apply, ← lin_single, P_eval_lin, map_zero]

omit hx in
theorem isSplittingField (Q : (field p x)[X])
    (hQ : Q.map (algebraMap _ (𝕂 n)) = (P p n).map (ι n)) :
    Q.IsSplittingField (field p x) (𝕂 n) := by
  rw [isSplittingField_iff_intermediateField, hQ, splits_iff_card_roots, roots_map_P,
    natDegree_map_eq_of_injective (IsFractionRing.injective _ _), natDegree_P, Multiset.card_map,
    Finset.card_val, Finset.card_image_of_injective _ (lin_injective p n)]
  refine ⟨by simp, eq_top_iff.2 fun y _ => ?_⟩
  set E := IntermediateField.adjoin (field p x) (Q.rootSet (𝕂 n))
  have h : ∀ a : MvPolynomial (Fin n) (ZMod p), (ι n) a ∈ E := fun a => by
    induction a using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (ZMod p) (field p x) (𝕂 n)]
      exact E.algebraMap_mem _
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f k hf =>
      rw [map_mul]
      refine mul_mem hf (IntermediateField.subset_adjoin _ _ ?_)
      rw [mem_rootSet', hQ, aeval_def, ← eval_map, hQ, eval_map_P_X]
      exact ⟨Monic.ne_zero ((P_monic p n).map _), rfl⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin n) (ZMod p)) y
  exact div_mem (h a) (h b)

/-- `𝔽_p(X₁, …, Xₙ)` is Galois over `𝔽_p(x)`: it is the splitting field of `∏ (T − λ · X)`,
separable since its derivative is the constant `A₀ = ±Δₙ^{p−1} ≠ 0`. -/
theorem isGalois : IsGalois (field p x) (𝕂 n) := by
  obtain ⟨Q, hQ⟩ := exists_map_eq_P p x hx
  have := isSplittingField p x Q hQ
  refine IsGalois.of_separable_splitting_field (p := Q) ?_
  rw [← separable_map (algebraMap _ (𝕂 n)), hQ, separable_def, derivative_map, derivative_P,
    map_C]
  have hc : (ι n) (A p n 0) ≠ 0 := by
    rw [A_zero, (IsFractionRing.injective _ _).ne_iff' (map_zero _)]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (pow_ne_zero _ (Δ_ne_zero p n))
  exact ⟨0, C ((ι n) (A p n 0))⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hc, C_1]⟩

/-- **Every automorphism of `𝔽_p(X)` over `𝔽_p(x)` is some `g ∈ GLₙ(𝔽_p)`**: it sends each
`X_k` to a root `λ · X` of `∏ (T − λ · X)`. Hence a polynomial invariant under those `g` that
fix `𝔽_p(x)` lies in `𝔽_p(x)`. -/
theorem mem_field (f : MvPolynomial (Fin n) (ZMod p))
    (hf : ∀ g : Matrix (Fin n) (Fin n) (ZMod p), IsUnit g.det →
      (∀ a, (ι n) a ∈ field p x → MvPolynomial.aeval (act p g MvPolynomial.X) a = a) →
      MvPolynomial.aeval (act p g MvPolynomial.X) f = f) :
    (ι n) f ∈ field p x := by
  obtain ⟨Q, hQ⟩ := exists_map_eq_P p x hx
  have := isSplittingField p x Q hQ
  have := isGalois p x hx
  have := IsSplittingField.finiteDimensional (𝕂 n) Q
  have hfix := (IsGalois.mem_bot_iff_fixed ((ι n) f)).2 fun σ => by
    have hroot : ∀ k, ∃ l : Fin n → ZMod p,
        σ ((ι n) (MvPolynomial.X k)) = (ι n) (lin p l) := fun k => by
      have hmem : σ ((ι n) (MvPolynomial.X k)) ∈ ((P p n).map (ι n)).roots := by
        rw [mem_roots ((P_monic p n).map _).ne_zero, IsRoot.def, ← hQ, eval_map_algebraMap,
          aeval_algHom_apply, ← eval_map_algebraMap, hQ, eval_map_P_X, map_zero]
      rw [roots_map_P] at hmem
      obtain ⟨a, ha, h⟩ := Multiset.mem_map.1 hmem
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨l, h.symm⟩
    choose l hl using hroot
    have hcomp : ∀ a, σ ((ι n) a) = (ι n) (MvPolynomial.aeval (act p (of l) MvPolynomial.X) a) := by
      intro a
      have : (σ : (𝕂 n) →+* (𝕂 n)).comp (ι n) =
          (ι n).comp (MvPolynomial.aeval (act p (of l) MvPolynomial.X)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r; rw [← ZMod.natCast_zmod_val r]; simp only [map_natCast]
        · intro k; simp [hl, act, lin]
      exact RingHom.congr_fun this a
    have hg : IsUnit (of l).det := by
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      obtain ⟨v, hv, hv0⟩ := exists_vecMul_eq_zero_iff.2 h0
      have h := hcomp (lin p v)
      rw [aeval_act_lin, hv0, show lin p (0 : Fin n → ZMod p) = 0 by simp [lin], map_zero,
        map_eq_zero_iff σ σ.injective, map_eq_zero_iff _ (IsFractionRing.injective _ _),
        show (0 : MvPolynomial (Fin n) (ZMod p)) = lin p 0 by simp [lin]] at h
      exact hv (lin_injective p n h)
    rw [hcomp, hf _ hg fun a ha => IsFractionRing.injective _ (𝕂 n) <| by
      rw [← hcomp]; exact σ.commutes ⟨_, ha⟩]
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 hfix
  exact hy ▸ y.2

/-- **`𝔽_p[x]` is integrally closed in `𝔽_p[X]` relative to `𝔽_p(x)`**: a polynomial whose image
lies in `𝔽_p(x)` lies in `𝔽_p[x]`, since `𝔽_p[x]` is a polynomial algebra (hence normal) over
which `𝔽_p[X]` is integral. -/
theorem mem_adjoin_of_mem_field (f : MvPolynomial (Fin n) (ZMod p)) (hf : (ι n) f ∈ field p x) :
    f ∈ Algebra.adjoin (ZMod p) (Set.range x) := by
  set ι' := IsScalarTower.toAlgHom (ZMod p) (MvPolynomial (Fin n) (ZMod p)) (𝕂 n)
  have hι : Function.Injective ι' := IsFractionRing.injective _ _
  set B := Algebra.adjoin (ZMod p) (Set.range ((ι n) ∘ x))
  have hB : B = (Algebra.adjoin (ZMod p) (Set.range x)).map ι' := (map_adjoin_eq p x).symm
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv
    ((algebraicIndependent_of p x hx).map' hι).aevalEquiv.toRingEquiv
  have hint : IsIntegral B ((ι n) f) := by
    have h := isIntegral_aeval p (ι' ∘ MvPolynomial.X) B (fun i => by
      rw [← MvPolynomial.aeval_unique ι', hB]
      exact Subalgebra.mem_map.2 ⟨_, hx i, rfl⟩) f
    rwa [← MvPolynomial.aeval_unique ι'] at h
  obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.1 hf
  have hfB : (ι n) f ∈ B := by
    by_cases hs0 : s = 0
    · rw [hrs, hs0, div_zero]; exact zero_mem _
    have hinj : Function.Injective (Algebra.ofId B (𝕂 n)) := fun _ _ h => Subtype.ext h
    let j := IsFractionRing.liftAlgHom (K := FractionRing B) hinj
    have hj : j (IsLocalization.mk' _ (⟨r, hr⟩ : B)
        ⟨⟨s, hs⟩, mem_nonZeroDivisors_of_ne_zero fun h => hs0 (congrArg Subtype.val h)⟩) =
          (ι n) f := by
      simp only [j, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_mk', hrs]; rfl
    rw [← hj] at hint
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1
      ((isIntegral_algHom_iff j j.toRingHom.injective).1 hint)
    rw [← hj, ← hb]
    simp only [j, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    exact b.2
  obtain ⟨c, hc, hcf⟩ := Subalgebra.mem_map.1 (hB ▸ hfB)
  rwa [← hι hcf]

end

/-- **Dickson's theorem** (pages 9–11): `𝔽_p[X₁, …, Xₙ]^{GLₙ(𝔽_p)} = 𝔽_p[A₀, …, A_{n−1}]`.
A polynomial is invariant under every `g ∈ GLₙ(𝔽_p)`, acting by `X_j ↦ Σ_k g_{jk} X_k`, iff it
lies in the subalgebra generated by the Dickson invariants; this subalgebra is a polynomial
algebra on them (`dickson_algebraicIndependent`). -/
theorem dickson_theorem {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) :
    (∀ g : Matrix (Fin n) (Fin n) (ZMod p), IsUnit g.det →
      MvPolynomial.aeval (act p g MvPolynomial.X) f = f) ↔
      f ∈ Algebra.adjoin (ZMod p) (Set.range (dickson p n)) := by
  have hx : ∀ i, dickson p n i ∈ Algebra.adjoin (ZMod p) (Set.range (dickson p n)) :=
    fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  refine ⟨fun hf => mem_adjoin_of_mem_field p _ hx f
    (mem_field p _ hx f fun g hg _ => hf g hg), fun hf g hg => ?_⟩
  induction hf using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact aeval_act_dickson p g hg i
  | algebraMap r => exact MvPolynomial.aeval_C _ _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/-! #### The `SL` variant (pages 11–12) -/

/-- The generators `Δₙ, A₁, …, A_{n−1}` of the `SLₙ(𝔽_p)`-invariants. -/
noncomputable def dicksonSL (n : ℕ) (i : Fin n) : MvPolynomial (Fin n) (ZMod p) :=
  if (i : ℕ) = 0 then Δ p n else A p n i

theorem aeval_act_Δ {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod p)) :
    MvPolynomial.aeval (act p g MvPolynomial.X) (Δ p n) = MvPolynomial.C g.det * Δ p n := by
  rw [Δ, ← AlgHom.coe_toRingHom, map_moore, ← MvPolynomial.algebraMap_eq, ← moore_act]
  congr 1; ext; simp

theorem dickson_mem_adjoin_SL {n : ℕ} (i : Fin n) :
    dickson p n i ∈ Algebra.adjoin (ZMod p) (Set.range (dicksonSL p n)) := by
  by_cases hi : (i : ℕ) = 0
  · have h : Δ p n ∈ Algebra.adjoin (ZMod p) (Set.range (dicksonSL p n)) :=
      Algebra.subset_adjoin ⟨i, by simp [dicksonSL, hi]⟩
    rw [dickson, hi, A_zero]
    exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (pow_mem h _)
  · exact Algebra.subset_adjoin ⟨i, by simp [dicksonSL, dickson, hi]⟩

/-- `Δₙ, A₁, …, A_{n−1}` are algebraically independent. -/
theorem dicksonSL_algebraicIndependent (n : ℕ) :
    AlgebraicIndependent (ZMod p) (dicksonSL p n) :=
  algebraicIndependent_of p _ (dickson_mem_adjoin_SL p)

/-- **The `SL` variant** (pages 11–12):
`𝔽_p[X₁, …, Xₙ]^{SLₙ(𝔽_p)} = 𝔽_p[Δₙ, A₁, …, A_{n−1}]`, a polynomial algebra
(`dicksonSL_algebraicIndependent`). -/
theorem dickson_theorem_SL {n : ℕ} (f : MvPolynomial (Fin n) (ZMod p)) :
    (∀ g : Matrix (Fin n) (Fin n) (ZMod p), g.det = 1 →
      MvPolynomial.aeval (act p g MvPolynomial.X) f = f) ↔
      f ∈ Algebra.adjoin (ZMod p) (Set.range (dicksonSL p n)) := by
  have hx := dickson_mem_adjoin_SL p (n := n)
  refine ⟨fun hf => mem_adjoin_of_mem_field p _ hx f (mem_field p _ hx f fun g _ hfix => hf g ?_),
    fun hf g hg => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact det_isEmpty
    have h := hfix (Δ p n) (IntermediateField.subset_adjoin _ _ ⟨⟨0, hn⟩, by simp [dicksonSL]⟩)
    rw [aeval_act_Δ] at h
    have := mul_right_cancel₀ (Δ_ne_zero p n) (h.trans (one_mul _).symm)
    exact MvPolynomial.C_injective _ _ (this.trans MvPolynomial.C_1.symm)
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx; unfold dicksonSL; split_ifs
    · rw [aeval_act_Δ, hg, map_one, one_mul]
    · exact aeval_act_dickson p g (hg ▸ isUnit_one) i
  | algebraMap r => exact MvPolynomial.aeval_C _ _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

end Grothendieck.Folder160
