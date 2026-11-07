module

public import Mathlib

@[expose] public section


/-!
# Folder 40, pages 26–27: regularity is not stable under the group law of `H¹(A, α_p)`

The modernised reading `transcripts/40/40.modern.tex` (§ « Une remarque sur les
revêtements de k[[X]] ») takes `A = k[[X]]` and the `α_p`-torsors `A[T]/(T^p - f)`,
`f ∉ A^p`. It states:

> `A[T]/(T^p - X^n)` is a regular local ring if `n = 1`, and not otherwise. For the
> group law of `H¹(A, α_p) = A/A^p`, the non-regular torsor of `p`-th roots of `X²`
> is the sum of the two regular torsors of `p`-th roots of `X` and of `-X + X²`.
> Regularity does not even pass to the fibre product: `C₁ ⊗_A C₂ ≃ C₁[T]/(T^p)` has
> nilpotents, since in `C₁` one has `X = s^p` and `-X + X² = (-s + s²)^p`.

This is finding `40-alpha-p-regular-sum` of `src/content/findings.ts`. Proving it says
only that the claims hold as stated; whether they stand in the literature is a separate
question.

What is formalised.

* `isDVR_adjoinRoot` (the regular torsors): over any discrete valuation ring `A` with
  uniformiser `ϖ`, any unit `u` and any `n ≥ 1`, `A[T]/(T^n - ϖu)` is a discrete
  valuation ring. No completeness, no characteristic, `n` arbitrary. The proof: the
  polynomial is Eisenstein, hence prime in the factorial ring `A[T]`; the extension is
  integral, so every maximal ideal contracts to `(ϖ)`, contains `T` (as `T^n = ϖu`) and is
  contained in `(T)` (write an element as `a + T b`; then `a ∈ (ϖ) ⊆ (T)`); so the ring is
  local with principal maximal ideal `(T)`, and Noetherian. Instances:
  `isDVR_root_X` (`T^n = X`) and `isDVR_root_neg_X_add_X_sq` (`T^n = -X + X²`, as
  `-X + X² = X (X - 1)` with `X - 1` a unit) over `k[[X]]`, `k` any field.
* `cusp_not_valuation` and `not_isDVR_cusp_odd` (the sum): for `n ≥ 3` odd and `k` any
  field, in `S = k[[X]][T]/(T^n - X²)` neither of `X`, `T` divides the other, so `S` is
  not a discrete valuation ring (not even a valuation ring). The witness is the map
  `S → k[[Z]]`, `X ↦ Zⁿ`, `T ↦ Z²`, whose image has no coefficient at an odd exponent
  `< n`: `T ∣ X` would put `Z^(n-2)` in it. For `n` even, `not_isDomain_cusp_even`: `S`
  is not even a domain (`(T^(n/2) - X)(T^(n/2) + X) = 0`, both factors nonzero), and for
  `n = 2` in characteristic `2`, `cusp_two_nilpotent`: `(T - X)² = 0` with `T - X ≠ 0`.
* `fibre_nilpotent` and `fibre_ne_zero` (the fibre product): in characteristic `p`, with
  `C₁ = A[T]/(T^p - X)`, `C₂ = A[T]/(T^p + X - X²)` and `s`, `t` their roots,
  `z = 1 ⊗ t + (s - s²) ⊗ 1` satisfies `z^p = 0` in `C₁ ⊗_A C₂` and `z ≠ 0` (its image in
  `C₁[T]/(T^p + X - X²)` is the class of the monic `T + s - s²` of degree `1 < p`).
  `neg_X_add_X_sq_eq_pow` is the identity `-X + X² = (-s + s²)^p` in `C₁`.

The isomorphism `C₁ ⊗_A C₂ ≃ C₁[T]/(T^p)` itself is not formalised, nor is the
identification of the group law of `H¹(A, α_p)` with addition in `A/A^p`.
-/

namespace Grothendieck.Folder40

open Polynomial IsLocalRing

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- `T^n - ϖu` is Eisenstein at the maximal ideal, hence irreducible. -/
theorem irreducible_radical {n : ℕ} (hn : n ≠ 0) {ϖ u : A} (hϖ : Irreducible ϖ)
    (hu : IsUnit u) : Irreducible (X ^ n - C (ϖ * u)) := by
  have hm := monic_X_pow_sub_C (ϖ * u) hn
  have hdeg : (X ^ n - C (ϖ * u)).natDegree = n := natDegree_X_pow_sub_C
  refine IsEisensteinAt.irreducible (𝓟 := maximalIdeal A) ⟨?_, ?_, ?_⟩
    (maximalIdeal.isMaximal A).isPrime hm.isPrimitive (by omega)
  · rw [hm.leadingCoeff]; exact fun h => (maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr h)
  · intro m hmn
    have hne : m ≠ n := by omega
    simp only [coeff_sub, coeff_X_pow, coeff_C, hne, ↓reduceIte, zero_sub]
    split_ifs with h0
    · rw [hϖ.maximalIdeal_eq]
      exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ))
    · simp
  · simp only [coeff_sub, coeff_X_pow, coeff_C, (Ne.symm hn), ↓reduceIte, zero_sub]
    rw [neg_mem_iff, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have : u = ϖ * c := mul_left_cancel₀ hϖ.ne_zero (by rw [hc]; ring)
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hu))

theorem isDomain_radical {n : ℕ} (hn : n ≠ 0) {ϖ u : A} (hϖ : Irreducible ϖ)
    (hu : IsUnit u) : IsDomain (AdjoinRoot (X ^ n - C (ϖ * u))) :=
  AdjoinRoot.isDomain_of_prime (irreducible_radical hn hϖ hu).prime

/-- **The regular torsors.** Over a discrete valuation ring `A` with uniformiser `ϖ`,
`A[T]/(T^n - ϖu)` is a discrete valuation ring for every `n ≥ 1` and every unit `u`. -/
theorem isDVR_adjoinRoot {n : ℕ} (hn : n ≠ 0) {ϖ u : A} (hϖ : Irreducible ϖ)
    (hu : IsUnit u) :
    have := isDomain_radical hn hϖ hu
    IsDiscreteValuationRing (AdjoinRoot (X ^ n - C (ϖ * u))) := by
  set g : A[X] := X ^ n - C (ϖ * u) with hg_def
  have := isDomain_radical hn hϖ hu
  have hg : g.Monic := monic_X_pow_sub_C (ϖ * u) hn
  set y := AdjoinRoot.root g
  have hy : y ^ n = AdjoinRoot.of g (ϖ * u) := by
    have := AdjoinRoot.eval₂_root g
    rw [hg_def, eval₂_sub, eval₂_X_pow, eval₂_C] at this
    exact sub_eq_zero.mp this
  obtain ⟨v, rfl⟩ := hu
  have hϖy : AdjoinRoot.of g ϖ ∈ Ideal.span {y} := by
    have : AdjoinRoot.of g ϖ = y ^ n * AdjoinRoot.of g ↑v⁻¹ := by
      rw [hy, ← map_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self y) n (Nat.pos_of_ne_zero hn))
  have hint : (algebraMap A (AdjoinRoot g)).IsIntegral := by
    have := (AdjoinRoot.powerBasis' hg).finite
    exact Algebra.IsIntegral.isIntegral
  have key : ∀ M : Ideal (AdjoinRoot g), M.IsMaximal → M = Ideal.span {y} := by
    intro M hM
    have hc' : M.comap (algebraMap A _) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ hint M)
    have hϖM : AdjoinRoot.of g ϖ ∈ M := by
      rw [← AdjoinRoot.algebraMap_eq, ← Ideal.mem_comap, hc', hϖ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self ϖ
    have hyM : y ∈ M :=
      hM.isPrime.mem_of_pow_mem n (by rw [hy, map_mul]; exact M.mul_mem_right _ hϖM)
    refine hM.eq_of_le ?_ ?_
    · exact fun h => hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hyM (Ideal.span_singleton_eq_top.mp h))
    · intro r hr
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective r
      have e : AdjoinRoot.root g = y := rfl
      rw [← X_mul_divX_add q, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, e] at hr ⊢
      have ha : AdjoinRoot.of g (q.coeff 0) ∈ M := by
        simpa using M.sub_mem hr (M.mul_mem_right (AdjoinRoot.mk g q.divX) hyM)
      obtain ⟨b, hb⟩ : ∃ b, b * ϖ = q.coeff 0 := by
        rwa [← Ideal.mem_span_singleton', ← hϖ.maximalIdeal_eq, ← hc', Ideal.mem_comap,
          AdjoinRoot.algebraMap_eq]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self y)) ?_
      rw [← hb, map_mul]
      exact Ideal.mul_mem_left _ _ hϖy
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (AdjoinRoot g)
  have hspan : (Ideal.span {y}).IsMaximal := key M hM ▸ hM
  have : IsLocalRing (AdjoinRoot g) :=
    IsLocalRing.of_unique_max_ideal ⟨_, hspan, fun I hI => key I hI⟩
  have hmax : maximalIdeal (AdjoinRoot g) = Ideal.span {y} :=
    (IsLocalRing.eq_maximalIdeal hspan).symm
  have : IsNoetherianRing (AdjoinRoot g) := inferInstanceAs (IsNoetherianRing (A[X] ⧸ _))
  have hpid : IsPrincipalIdealRing (AdjoinRoot g) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := AdjoinRoot g)).out 5 1).mp
      (by rw [hmax]; exact ⟨⟨y, rfl⟩⟩)
  have hy0 : y ≠ 0 := fun h => mul_ne_zero hϖ.ne_zero v.ne_zero <|
    AdjoinRoot.of.injective_of_degree_ne_zero (f := g)
      (by rw [hg_def, degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]; exact_mod_cast hn)
      (by rw [← hy, h, zero_pow hn, map_zero])
  exact { hpid, ‹IsLocalRing (AdjoinRoot g)› with
    not_a_field' := by rw [hmax]; simpa [Ideal.span_singleton_eq_bot] using hy0 }

end DVR

section PowerSeries

variable {k : Type*} [Field k]

/-- `k[[X]][T]/(T^n - X)` is a discrete valuation ring. -/
theorem isDVR_root_X {n : ℕ} (hn : n ≠ 0) :
    have := isDomain_radical hn PowerSeries.X_irreducible (isUnit_one (M := (PowerSeries k)))
    IsDiscreteValuationRing (AdjoinRoot (X ^ n - C (PowerSeries.X * 1 : (PowerSeries k)))) :=
  isDVR_adjoinRoot hn PowerSeries.X_irreducible isUnit_one

theorem isUnit_X_sub_one : IsUnit (PowerSeries.X - 1 : (PowerSeries k)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]; simp

/-- `k[[X]][T]/(T^n + X - X²)` is a discrete valuation ring: `-X + X² = X (X - 1)`. -/
theorem isDVR_root_neg_X_add_X_sq {n : ℕ} (hn : n ≠ 0) :
    have := isDomain_radical hn PowerSeries.X_irreducible (isUnit_X_sub_one (k := k))
    IsDiscreteValuationRing
      (AdjoinRoot (X ^ n - C (PowerSeries.X * (PowerSeries.X - 1) : (PowerSeries k)))) :=
  isDVR_adjoinRoot hn PowerSeries.X_irreducible isUnit_X_sub_one

theorem neg_X_add_X_sq : (-PowerSeries.X + PowerSeries.X ^ 2 : (PowerSeries k)) =
    PowerSeries.X * (PowerSeries.X - 1) := by ring

/-- The cusp `S = k[[X]][T]/(T^n - X²)`. -/
abbrev Cusp (k : Type*) [Field k] (n : ℕ) := AdjoinRoot (X ^ n - C (PowerSeries.X ^ 2 : (PowerSeries k)))

/-- Power series with no coefficient at an odd exponent `< n`: a subring. -/
def noOddBelow (n : ℕ) : Subring (PowerSeries k) where
  carrier := {g | ∀ m, Odd m → m < n → PowerSeries.coeff m g = 0}
  mul_mem' {a b} ha hb m hm hmn := by
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rcases Nat.even_or_odd x.1 with h | h
    · have h2 : Odd x.2 :=
        Nat.not_even_iff_odd.mp fun h2 => Nat.not_odd_iff_even.mpr (h.add h2) (hx ▸ hm)
      rw [hb _ h2 (by omega), mul_zero]
    · rw [ha _ h (by omega), zero_mul]
  one_mem' m hm _ := by
    rw [PowerSeries.coeff_one, ite_eq_right_iff]; rintro rfl; exact absurd hm Nat.not_odd_zero
  add_mem' {a b} ha hb m hm hmn := by rw [map_add, ha m hm hmn, hb m hm hmn, add_zero]
  zero_mem' m _ _ := by simp
  neg_mem' {a} ha m hm hmn := by rw [map_neg, ha m hm hmn, neg_zero]

/-- The substitution `X ↦ Zⁿ`. -/
noncomputable def substPow (n : ℕ) (hn : n ≠ 0) : (PowerSeries k) →+* (PowerSeries k) :=
  (PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow (R := k) hn)).toRingHom

theorem substPow_X (n : ℕ) (hn : n ≠ 0) :
    substPow (k := k) n hn PowerSeries.X = PowerSeries.X ^ n := by
  simp [substPow, PowerSeries.coe_substAlgHom, PowerSeries.subst_X
    (PowerSeries.HasSubst.X_pow (R := k) hn)]

theorem substPow_mem (n : ℕ) (hn : n ≠ 0) (a : (PowerSeries k)) : substPow n hn a ∈ noOddBelow n := by
  intro m hm hmn
  simp only [substPow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coe_substAlgHom]
  rw [PowerSeries.coeff_subst_X_pow hn, ite_eq_right_iff]
  rintro ⟨c, rfl⟩
  rcases c with _ | c
  · simp at hm
  · exfalso; nlinarith

/-- The map `S → k[[Z]]`, `X ↦ Zⁿ`, `T ↦ Z²`. -/
noncomputable def cuspMap (n : ℕ) (hn : n ≠ 0) : Cusp k n →+* (PowerSeries k) :=
  AdjoinRoot.lift (substPow n hn) (PowerSeries.X ^ 2) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, map_pow, substPow_X]; ring)

theorem cuspMap_mem (n : ℕ) (hn : n ≠ 0) (r : Cusp k n) : cuspMap n hn r ∈ noOddBelow n := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [cuspMap, AdjoinRoot.lift_mk]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add]; exact Subring.add_mem _ hp hq
  | monomial j a =>
    rw [eval₂_monomial]
    refine Subring.mul_mem _ (substPow_mem n hn a) fun m hm hmn => ?_
    rw [← pow_mul, PowerSeries.coeff_X_pow, ite_eq_right_iff]
    rintro rfl; exact absurd hm (Nat.not_odd_iff_even.mpr (even_two_mul j))

/-- **The sum is not regular.** For `n ≥ 3` odd, in `k[[X]][T]/(T^n - X²)` neither of `X`,
`T` divides the other. -/
theorem cusp_not_valuation {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (c : Cusp k n) :
    AdjoinRoot.of _ PowerSeries.X * c ≠ AdjoinRoot.root _ ∧
      AdjoinRoot.root _ * c ≠ AdjoinRoot.of _ PowerSeries.X := by
  have hn0 : n ≠ 0 := by omega
  have hX : cuspMap (k := k) n hn0 (AdjoinRoot.of _ PowerSeries.X) = PowerSeries.X ^ n := by
    rw [cuspMap, AdjoinRoot.lift_of, substPow_X]
  have hY : cuspMap (k := k) n hn0 (AdjoinRoot.root _) = PowerSeries.X ^ 2 := by
    rw [cuspMap, AdjoinRoot.lift_root]
  have hsplit : (PowerSeries.X ^ n : (PowerSeries k)) = PowerSeries.X ^ 2 * PowerSeries.X ^ (n - 2) := by
    rw [← pow_add]; congr 1; omega
  have hX2 : (PowerSeries.X ^ 2 : (PowerSeries k)) ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  constructor
  · intro h
    have h1 := congrArg (cuspMap n hn0) h
    rw [map_mul, hX, hY, hsplit, mul_assoc] at h1
    have h2 : PowerSeries.X ^ (n - 2) * cuspMap n hn0 c = 1 :=
      mul_left_cancel₀ hX2 (by rw [h1, mul_one])
    have h3 := congrArg PowerSeries.constantCoeff h2
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), zero_mul,
      map_one] at h3
    exact zero_ne_one h3
  · intro h
    have h1 := congrArg (cuspMap n hn0) h
    rw [map_mul, hX, hY, hsplit] at h1
    have h2 : cuspMap n hn0 c = PowerSeries.X ^ (n - 2) := mul_left_cancel₀ hX2 h1
    have h3 := cuspMap_mem n hn0 c (n - 2) (by
      obtain ⟨j, rfl⟩ := hodd; exact ⟨j - 1, by omega⟩) (by omega)
    rw [h2, PowerSeries.coeff_X_pow_self] at h3
    exact one_ne_zero h3

theorem not_isDVR_cusp_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    ¬ ∃ _ : IsDomain (Cusp k n), IsDiscreteValuationRing (Cusp k n) := by
  rintro ⟨_, _⟩
  obtain ⟨c, hc⟩ := ValuationRing.cond (AdjoinRoot.of _ PowerSeries.X : Cusp k n)
    (AdjoinRoot.root _)
  exact hc.elim (cusp_not_valuation hn hodd c).1 (cusp_not_valuation hn hodd c).2

theorem cusp_factor_ne_zero {m : ℕ} (hm : m ≠ 0) (ε : (PowerSeries k)) :
    AdjoinRoot.mk (X ^ (2 * m) - C (PowerSeries.X ^ 2 : (PowerSeries k))) (X ^ m + C ε) ≠ 0 := by
  have hmo : (X ^ m + C ε : (PowerSeries k)[X]).Monic := monic_X_pow_add_C ε hm
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (by omega))
    hmo.ne_zero ?_
  rw [natDegree_X_pow_sub_C, natDegree_X_pow_add_C]; omega

/-- For `n = 2m` even, `k[[X]][T]/(T^n - X²)` is not a domain. -/
theorem not_isDomain_cusp_even {m : ℕ} (hm : m ≠ 0) : ¬ IsDomain (Cusp k (2 * m)) := by
  intro hd
  have h0 : AdjoinRoot.mk (X ^ (2 * m) - C (PowerSeries.X ^ 2 : (PowerSeries k))) (X ^ m + C (-PowerSeries.X)) *
      AdjoinRoot.mk _ (X ^ m + C PowerSeries.X) = 0 := by
    rw [← map_mul, AdjoinRoot.mk_eq_zero]
    exact ⟨1, by rw [mul_one, map_neg, C_pow]; ring⟩
  exact mul_ne_zero (cusp_factor_ne_zero hm _) (cusp_factor_ne_zero hm _) h0

/-- For `n = 2` in characteristic `2`: `(T - X)² = 0` and `T - X ≠ 0`. -/
theorem cusp_two_nilpotent [CharP k 2] :
    (AdjoinRoot.root _ - AdjoinRoot.of _ PowerSeries.X : Cusp k 2) ^ 2 = 0 ∧
      (AdjoinRoot.root _ - AdjoinRoot.of _ PowerSeries.X : Cusp k 2) ≠ 0 := by
  have hr : (AdjoinRoot.root _ - AdjoinRoot.of _ PowerSeries.X : Cusp k 2) =
      AdjoinRoot.mk _ (X - C PowerSeries.X) := by
    rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rw [hr]
  refine ⟨?_, ?_⟩
  · rw [← map_pow, AdjoinRoot.mk_eq_zero]
    refine ⟨1, ?_⟩
    have h2 : (2 : (PowerSeries k)[X]) = 0 := by
      have := congrArg (algebraMap k (PowerSeries k)[X]) (CharP.cast_eq_zero k 2)
      rw [map_natCast, map_zero] at this; exact_mod_cast this
    rw [C_pow]
    linear_combination (C PowerSeries.X ^ 2 - X * C PowerSeries.X) * h2
  · refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (by omega))
      (X_sub_C_ne_zero _) ?_
    rw [natDegree_X_pow_sub_C, natDegree_X_sub_C]; omega

end PowerSeries

section Fibre

open TensorProduct

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- `C₁ = k[[X]][T]/(T^p - X)`. -/
abbrev C₁ := AdjoinRoot (X ^ p - C (PowerSeries.X : (PowerSeries k)))
/-- `C₂ = k[[X]][T]/(T^p - (-X + X²))`. -/
abbrev C₂ := AdjoinRoot (X ^ p - C (-PowerSeries.X + PowerSeries.X ^ 2 : (PowerSeries k)))

omit [CharP k p] in
instance isDomain_C₁ : IsDomain (C₁ (k := k) p) := by
  have := isDomain_radical hp.out.ne_zero PowerSeries.X_irreducible (isUnit_one (M := PowerSeries k))
  rwa [mul_one] at this

omit hp in
theorem natCast_p_eq_zero {R : Type*} [CommRing R] [Algebra (PowerSeries k) R] : (p : R) = 0 := by
  rw [← map_natCast (algebraMap (PowerSeries k) R), ← map_natCast (PowerSeries.C (R := k)),
    CharP.cast_eq_zero, map_zero, map_zero]

theorem charP_of_algebra {R : Type*} [CommRing R] [Algebra (PowerSeries k) R] [Nontrivial R] :
    CharP R p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (natCast_p_eq_zero (k := k) p)

/-- In `C₁`: `-X + X² = (-s + s²)^p`. -/
theorem neg_X_add_X_sq_eq_pow :
    AdjoinRoot.of _ (-PowerSeries.X + PowerSeries.X ^ 2) =
      (-AdjoinRoot.root _ + AdjoinRoot.root _ ^ 2 : C₁ (k := k) p) ^ p := by
  have := charP_of_algebra (k := k) p (R := C₁ (k := k) p)
  have hs : (AdjoinRoot.root _ : C₁ (k := k) p) ^ p = AdjoinRoot.of _ PowerSeries.X := by
    have := AdjoinRoot.eval₂_root (X ^ p - C (PowerSeries.X : (PowerSeries k)))
    rw [eval₂_sub, eval₂_X_pow, eval₂_C] at this
    exact sub_eq_zero.mp this
  have e : ∀ r : C₁ (k := k) p, -r + r ^ 2 = r ^ 2 - r := fun r => by ring
  rw [e, sub_pow_char, ← pow_mul, mul_comm, pow_mul, hs, map_add, map_neg, map_pow]
  ring

/-- `D = C₁[T]/(T^p + X - X²)`, the base change of `C₂` to `C₁`. -/
abbrev D := AdjoinRoot (X ^ p - C (AdjoinRoot.of (X ^ p - C (PowerSeries.X : PowerSeries k))
  (-PowerSeries.X + PowerSeries.X ^ 2)))

omit [CharP k p] in
instance nontrivial_D : Nontrivial (D (k := k) p) :=
  AdjoinRoot.nontrivial _
    (by rw [degree_X_pow_sub_C hp.out.pos]; exact_mod_cast hp.out.ne_zero)

omit hp [CharP k p] in
theorem root_D_pow : (AdjoinRoot.root _ : D (k := k) p) ^ p =
    algebraMap (PowerSeries k) (D (k := k) p) (-PowerSeries.X + PowerSeries.X ^ 2) := by
  have := AdjoinRoot.eval₂_root (X ^ p - C (AdjoinRoot.of (X ^ p - C (PowerSeries.X :
    PowerSeries k)) (-PowerSeries.X + PowerSeries.X ^ 2)))
  rw [eval₂_sub, eval₂_X_pow, eval₂_C] at this
  rw [sub_eq_zero.mp this, IsScalarTower.algebraMap_apply (PowerSeries k) (C₁ (k := k) p),
    AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq]

omit hp [CharP k p] in
theorem root_C₂_pow : (AdjoinRoot.root _ : C₂ (k := k) p) ^ p =
    algebraMap (PowerSeries k) (C₂ (k := k) p) (-PowerSeries.X + PowerSeries.X ^ 2) := by
  have := AdjoinRoot.eval₂_root (X ^ p - C (-PowerSeries.X + PowerSeries.X ^ 2 :
    PowerSeries k))
  rw [eval₂_sub, eval₂_X_pow, eval₂_C] at this
  rw [sub_eq_zero.mp this, AdjoinRoot.algebraMap_eq]

/-- The map `C₁ ⊗_A C₂ → C₁[T]/(T^p + X - X²)`. -/
noncomputable def toD :
    C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p →ₐ[PowerSeries k] D (k := k) p :=
  Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom (PowerSeries k) (C₁ (k := k) p) (D (k := k) p))
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (AdjoinRoot.root _) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, root_D_pow]
      exact sub_self _))

/-- The element `z = t + s - s²` of the fibre product `C₁ ⊗_A C₂`. -/
noncomputable def z : C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p :=
  (1 : C₁ (k := k) p) ⊗ₜ AdjoinRoot.root _ -
    (-AdjoinRoot.root _ + AdjoinRoot.root _ ^ 2 : C₁ (k := k) p) ⊗ₜ 1

omit hp [CharP k p] in
theorem toD_z : toD p (z (k := k) p) =
    AdjoinRoot.mk _ (X - C (-AdjoinRoot.root _ + AdjoinRoot.root _ ^ 2)) := by
  rw [z, map_sub, toD, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, one_mul, mul_one,
    map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.liftAlgHom_root]
  rfl

omit [CharP k p] in
/-- **The fibre product is not reduced.** `z ≠ 0`. -/
theorem fibre_ne_zero : z (k := k) p ≠ 0 := fun h => by
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ hp.out.ne_zero)
    (X_sub_C_ne_zero _) ?_ ((toD_z (k := k) p).symm.trans (by rw [h, map_zero]))
  rw [natDegree_X_pow_sub_C, natDegree_X_sub_C]; exact hp.out.one_lt

/-- **The fibre product is not reduced.** `z^p = 0`. -/
theorem fibre_nilpotent : z (k := k) p ^ p = 0 := by
  have : Nontrivial (C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p) :=
    (toD (k := k) p).toRingHom.domain_nontrivial
  have := charP_of_algebra (k := k) p (R := C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p)
  rw [z, sub_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    one_pow, one_pow, ← neg_X_add_X_sq_eq_pow, root_C₂_pow, ← AdjoinRoot.algebraMap_eq,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul, sub_self]

end Fibre

end Grothendieck.Folder40

/-!
## The fibre product is `C₁[T]/(T^p)`

Added 2026-10-25. The isomorphism of page 27, `C₁ ⊗_A C₂ ≃ C₁[T]/(T^p)`, as an isomorphism
of `C₁`-algebras sending `z = 1 ⊗ t - (-s + s²) ⊗ 1` to the class of `T`. Forward:
`x ⊗ y ↦ x · φ(y)`, with `φ : C₂ → C₁[T]/(T^p)`, `t ↦ T + (-s + s²)`, well defined since
`(T + b)^p = T^p + b^p = -X + X²` (`add_pow_char`, `neg_X_add_X_sq_eq_pow`). Backward:
`T ↦ z`, well defined by `fibre_nilpotent`. The two composites are the identity on
generators.
-/

namespace Grothendieck.Folder40

open Polynomial TensorProduct

section FibreIso

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- `E = C₁[T]/(T^p)`. -/
abbrev E := AdjoinRoot (X ^ p : (C₁ (k := k) p)[X])

/-- `b = -s + s²` in `C₁`. -/
noncomputable abbrev b : C₁ (k := k) p := -AdjoinRoot.root _ + AdjoinRoot.root _ ^ 2

omit [CharP k p] in
instance nontrivial_E : Nontrivial (E (k := k) p) :=
  AdjoinRoot.nontrivial _ (by rw [degree_X_pow]; exact_mod_cast hp.out.ne_zero)

/-- In `C₁[T]/(T^p)`: `(T + c)^p = c^p`. -/
theorem root_add_pow_E (c : E (k := k) p) : (AdjoinRoot.root _ + c) ^ p = c ^ p := by
  have := charP_of_algebra (k := k) p (R := E (k := k) p)
  have hr := AdjoinRoot.eval₂_root (X ^ p : (C₁ (k := k) p)[X])
  rw [eval₂_X_pow] at hr
  rw [add_pow_char, hr, zero_add]

set_option backward.proofsInPublic true in
/-- `C₂ → C₁[T]/(T^p)`, `t ↦ T + b`. -/
noncomputable def C₂toE : C₂ (k := k) p →ₐ[PowerSeries k] E (k := k) p :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (AdjoinRoot.root _ + algebraMap _ _ (b p)) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, root_add_pow_E, ← map_pow,
      ← neg_X_add_X_sq_eq_pow (k := k), sub_eq_zero, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply (PowerSeries k) (C₁ (k := k) p) (E (k := k) p)]
    rfl)

/-- `C₁ ⊗_A C₂ → C₁[T]/(T^p)`, `x ⊗ y ↦ x · φ(y)`. -/
noncomputable def fibreToE :
    C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p →ₐ[C₁ (k := k) p] E (k := k) p :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (C₂toE p) (fun _ _ => Commute.all _ _)

/-- `C₁[T]/(T^p) → C₁ ⊗_A C₂`, `T ↦ z`. -/
noncomputable def EtoFibre :
    E (k := k) p →ₐ[C₁ (k := k) p] C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (z p) (by
    rw [eval₂_X_pow]; exact fibre_nilpotent p)

theorem fibreToE_z : fibreToE p (z (k := k) p) = AdjoinRoot.root _ := by
  simp [z, fibreToE, C₂toE]

theorem EtoFibre_root : EtoFibre p (AdjoinRoot.root _) = z (k := k) p :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **Page 27: the fibre product is `C₁[T]/(T^p)`.** `C₁ ⊗_A C₂ ≃ C₁[T]/(T^p)` as
`C₁`-algebras, `z = 1 ⊗ t - (-s + s²) ⊗ 1 ↦ T`. -/
noncomputable def fibreEquiv :
    C₁ (k := k) p ⊗[PowerSeries k] C₂ (k := k) p ≃ₐ[C₁ (k := k) p] E (k := k) p :=
  AlgEquiv.ofAlgHom (fibreToE p) (EtoFibre p)
    (AdjoinRoot.algHom_ext (by rw [AlgHom.comp_apply, EtoFibre_root, fibreToE_z,
      AlgHom.id_apply]))
    (Algebra.TensorProduct.ext (Algebra.ext_id _ _ _) (AdjoinRoot.algHom_ext (by
      have h : (1 : C₁ (k := k) p) ⊗ₜ[PowerSeries k] (AdjoinRoot.root _ : C₂ (k := k) p) =
          z p + algebraMap (C₁ (k := k) p) _ (b p) := by simp [z]
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars',
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply, h, map_add, AlgHom.commutes,
        fibreToE_z, EtoFibre_root])))

theorem fibreEquiv_z : fibreEquiv p (z (k := k) p) = AdjoinRoot.root _ := fibreToE_z p

end FibreIso

end Grothendieck.Folder40
