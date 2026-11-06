module

public import Mathlib

@[expose] public section


/-!
# Folder 90, page 9: a flat irreducible group whose components have non-empty fibres, and a
saturation that is not finitely generated

The modernised reading `transcripts/90/90.modern.tex` states on page 1 a Lemma 1 on
saturations in a torsion-free module over a Dedekind ring, and on page 9 a Proposition for a
flat affine group `G` over a Dedekind ring `A`, whose parenthesis says:

> cela signifie que pour les composantes irréd. de G, leurs fibres sont non vides

namely that the algebra `B` of `G` satisfies the conditions of Lemma 1 (the saturation of a
finitely generated submodule is finitely generated) exactly when every irreducible component of
`G` has non-empty fibres. This is finding `90-components-criterion`. Without finite type it
fails. Over a discrete valuation ring `R` with fraction field `K` and uniformiser `ϖ`, let

  `B = {f ∈ K[T] : f(0) ∈ R}`,

the union of the dilatations `R[T/ϖⁿ]` of `𝔾_a` at the origin. Proved here:

* `B`, a subalgebra of `K[T]`, is a domain, so `Spec B` is irreducible;
* `flat`: `B` is flat over `R` (torsion-free over a principal ideal domain);
* `residue_surjective`, `ker_residue`: `f ↦ f(0) mod ϖ` maps `B` onto the residue field with
  kernel `ϖB`, so `B/ϖB ≅ k`: the special fibre is a point;
* `generic_nontrivial`: `K ⊗_R B ≠ 0`: the generic fibre is non-empty;
* `comul`: for `f ∈ B`, `f(x + y) = Σᵢ bᵢ(x) cᵢ(y)` with `bᵢ, cᵢ ∈ B`, for all `x, y ∈ K`:
  the comultiplication of `𝔾_a` preserves `B`;
* `saturation_eq`, `not_fg_saturation`: the saturation of `R · T` in `B` is `K · T`, which is
  not a finitely generated `R`-module.

**What the formalisation finds.** The parenthesis fails without finite type: `Spec B` is
irreducible, flat, with both fibres non-empty, and still the saturation of a cyclic submodule
is not finitely generated. That `B` is a Hopf algebra is checked only through the
comultiplication identity, pointwise on `K` (an infinite field, so the identity is one of
polynomials); the antipode and counit are not written out.

**The edition's argument in finite type, reduced case.** For `π` in a commutative ring `A`,
write `d(A) = ⋂ₙ πⁿA`. Proved here, as a statement of the edition (not of the page):

* `iInf_pow_ne_bot_of_minimalPrime`: if a minimal prime `𝔭` satisfies `𝔭 + πA = A` (the
  component `V(𝔭)` misses the special fibre), then `d(A) ≠ 0`; no Noetherian hypothesis;
* `iInf_pow_eq_bot_of_minimalPrimes`: if `A` is Noetherian and reduced and every minimal prime
  meets `V(π)`, then `d(A) = 0` (Krull's intersection theorem in each `A/𝔭`);
* `iInf_pow_eq_bot_iff`: hence, for `A` Noetherian and reduced, `d(A) = 0` if and only if every
  irreducible component of `Spec A` meets the special fibre.

Remark, not formalised: for `A = R[G]` with `G` flat affine of finite type over a complete
discrete valuation ring, Hai–dos Santos II (arXiv:1802.06377), Prop. 6.19, together with
Kaplansky's theorem on projective modules, turn `d(A) = 0` into « `G` specially locally finite »
and « `R[G]` free over `R` », which gives the criterion of page 9 in the reduced case. The
non-reduced case stays open.
-/

open Polynomial TensorProduct

namespace Grothendieck.Folder90

variable (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]

/-- `B = {f ∈ K[T] : f(0) ∈ R}`. -/
def B : Subalgebra R K[X] where
  carrier := {f | f.coeff 0 ∈ (algebraMap R K).range}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, mul_coeff_zero] at *
    exact Subring.mul_mem _ hf hg
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, coeff_add] at *
    exact Subring.add_mem _ hf hg
  algebraMap_mem' r := ⟨r, by simp [Polynomial.algebraMap_apply]⟩

variable {R K}

theorem mem_B {f : K[X]} : f ∈ B R K ↔ ∃ r : R, algebraMap R K r = f.coeff 0 := Iff.rfl

theorem C_mul_X_mem (c : K) : C c * X ∈ B R K := ⟨0, by simp⟩

variable (R K) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- `B` is a domain: `Spec B` is irreducible. -/
example : IsDomain (B R K) := inferInstance

/-- **`B` is flat over `R`.** -/
theorem flat : Module.Flat R (B R K) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  refine eq_bot_iff.2 fun b hb => ?_
  obtain ⟨⟨r, hr⟩, hrb⟩ := (Submodule.mem_torsion_iff b).1 hb
  have hr0 : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.ne_zero hr)
  have h : C (algebraMap R K r) * (b : K[X]) = 0 := by
    have := congrArg Subtype.val hrb
    simpa [Algebra.smul_def, Polynomial.algebraMap_apply] using this
  rw [Submodule.mem_bot]
  exact Subtype.ext ((mul_eq_zero.1 h).resolve_left (by simpa using hr0))

/-- `R ≅ (algebraMap R K).range`. -/
noncomputable def rangeEquiv : R ≃+* (algebraMap R K).range :=
  RingEquiv.ofBijective (algebraMap R K).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective R K (congrArg Subtype.val h),
      (algebraMap R K).rangeRestrict_surjective⟩

/-- `f ↦ f(0) ∈ R`. -/
noncomputable def ev0 : B R K →+* R :=
  (rangeEquiv R K).symm.toRingHom.comp
    ((constantCoeff.comp (B R K).val.toRingHom).codRestrict _ fun f => by
      obtain ⟨r, hr⟩ := mem_B.1 f.2
      exact ⟨r, by simpa [coeff_zero_eq_eval_zero] using hr⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem algebraMap_ev0 (f : B R K) : algebraMap R K (ev0 R K f) = (f : K[X]).coeff 0 := by
  change ((rangeEquiv R K) (ev0 R K f) : K) = _
  rw [ev0, RingEquiv.toRingHom_eq_coe, RingHom.comp_apply, RingHom.coe_coe,
    RingEquiv.apply_symm_apply]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem ev0_algebraMap (r : R) : ev0 R K (algebraMap R (B R K) r) = r :=
  IsFractionRing.injective R K (by
    rw [algebraMap_ev0]
    simp [Polynomial.algebraMap_apply])

/-- The reduction `f ↦ f(0) mod ϖ`, from `B` to the residue field. -/
noncomputable def residueB : B R K →+* IsLocalRing.ResidueField R :=
  (IsLocalRing.residue R).comp (ev0 R K)

theorem residue_surjective : Function.Surjective (residueB R K) := fun x => by
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨algebraMap R (B R K) r, by simp [residueB, ev0_algebraMap]⟩

/-- **`B/ϖB = k`**: the kernel of the reduction is `ϖB`. -/
theorem ker_residue {ϖ : R} (hϖ : Irreducible ϖ) :
    RingHom.ker (residueB R K) = Ideal.span {algebraMap R (B R K) ϖ} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton']
  constructor
  · intro hf
    have hm : ev0 R K f ∈ IsLocalRing.maximalIdeal R := by
      simpa [residueB, IsLocalRing.residue_eq_zero_iff] using hf
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨a, ha⟩ := hm
    have hϖ0 : algebraMap R K ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero
    refine ⟨⟨C (algebraMap R K ϖ)⁻¹ * f, ⟨a, ?_⟩⟩, Subtype.ext ?_⟩
    · rw [mul_coeff_zero, coeff_C_zero, ← algebraMap_ev0, ← ha, map_mul,
        mul_comm (algebraMap R K a), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
    · simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Polynomial.algebraMap_apply]
      rw [mul_comm, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hϖ0, C_1, one_mul]
  · rintro ⟨g, rfl⟩
    simp only [residueB, RingHom.comp_apply, map_mul, ev0_algebraMap]
    rw [(IsLocalRing.residue_eq_zero_iff ϖ).2
      (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ),
      mul_zero]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **The generic fibre is non-empty**: `K ⊗_R B ≠ 0`. -/
theorem generic_nontrivial : Nontrivial (K ⊗[R] B R K) := by
  let φ : K ⊗[R] B R K →ₗ[R] K[X] := TensorProduct.lift
    (LinearMap.mk₂ R (fun (k : K) (b : B R K) => C k * (b : K[X]))
      (fun _ _ _ => by simp [add_mul]) (fun r k b => by
        simp [Algebra.smul_def, Polynomial.algebraMap_apply, mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun r k b => by
        simp [Algebra.smul_def, Polynomial.algebraMap_apply]
        ring))
  refine ⟨⟨1 ⊗ₜ 1, 0, fun h => ?_⟩⟩
  have := congrArg φ h
  simp [φ] at this

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **The comultiplication preserves `B`**: `f(x + y) = Σᵢ bᵢ(x) cᵢ(y)` with `bᵢ, cᵢ ∈ B`. -/
theorem comul (f : K[X]) (hf : f ∈ B R K) :
    ∃ (s : Finset (ℕ × ℕ)) (b c : ℕ × ℕ → K[X]), (∀ i, b i ∈ B R K) ∧ (∀ i, c i ∈ B R K) ∧
      ∀ x y : K, f.eval (x + y) = ∑ i ∈ s, (b i).eval x * (c i).eval y := by
  classical
  obtain ⟨r, hr⟩ := mem_B.1 hf
  -- index `(k, j)`: the term `f_k binom(k, j) x^j y^(k-j)`
  refine ⟨(Finset.range (f.natDegree + 1)) ×ˢ (Finset.range (f.natDegree + 1)),
    fun i => if i.2 = 0 then (if i.1 = 0 then C (f.coeff 0) else 1)
      else C (f.coeff i.1 * (i.1.choose i.2 : K)) * X ^ i.2,
    fun i => if i.2 = 0 then (if i.1 = 0 then 1 else C (f.coeff i.1) * X ^ i.1)
      else X ^ (i.1 - i.2), ?_, ?_, ?_⟩
  · intro i
    dsimp only
    split_ifs with h1 h2
    · exact ⟨r, by simp [hr]⟩
    · exact Subalgebra.one_mem _
    · exact ⟨0, by simp [coeff_X_pow, Ne.symm h1]⟩
  · intro i
    dsimp only
    split_ifs with h1 h2
    · exact Subalgebra.one_mem _
    · exact ⟨0, by simp [coeff_X_pow, Ne.symm h2]⟩
    · exact Subalgebra.pow_mem _ (mem_B.2 ⟨0, by simp⟩) _
  · intro x y
    rw [eval_eq_sum_range, Finset.sum_product]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ≤ f.natDegree + 1 := by simpa [Nat.lt_succ_iff] using hk
    rw [add_pow, Finset.mul_sum, ← Finset.sum_subset (Finset.range_subset_range.2 hk')]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp
        · simp [hk0.ne']
      · simp [hj0.ne']
        ring
    · intro j _ hj'
      have hkj : k < j := by simp at hj'; omega
      have hj0 : j ≠ 0 := by omega
      simp [Nat.choose_eq_zero_of_lt hkj, hj0]

/-- `T ∈ B`. -/
noncomputable def Xb : B R K := ⟨X, mem_B.2 ⟨0, by simp⟩⟩

/-- The saturation of `R · T` in `B`: the `b` with `r • b ∈ R · T` for some `r ≠ 0`. -/
def saturation : Set (B R K) :=
  {b | ∃ r : R, r ≠ 0 ∧ r • b ∈ Submodule.span R {Xb R K}}

/-- `K · T ⊂ B`, as an `R`-submodule. -/
def KT : Submodule R (B R K) where
  carrier := {b | ∃ c : K, (b : K[X]) = C c * X}
  add_mem' := by
    rintro _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by simp [hc, hd, add_mul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro r _ ⟨c, hc⟩
    exact ⟨algebraMap R K r * c, by
      simp [hc, Algebra.smul_def, Polynomial.algebraMap_apply, mul_assoc]⟩

/-- **The saturation of `R · T` is `K · T`.** -/
theorem saturation_eq : saturation R K = KT R K := by
  ext b
  constructor
  · rintro ⟨r, hr, hb⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hb
    have hr0 : algebraMap R K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hr
    refine ⟨(algebraMap R K r)⁻¹ * algebraMap R K a, ?_⟩
    have h := congrArg Subtype.val ha
    simp only [Algebra.smul_def] at h
    have h' : C (algebraMap R K r) * (b : K[X]) = C (algebraMap R K a) * X := by
      simpa [Xb, Polynomial.algebraMap_apply] using h.symm
    calc (b : K[X]) = C (algebraMap R K r)⁻¹ * (C (algebraMap R K r) * b) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hr0, C_1, one_mul]
      _ = _ := by rw [h', ← mul_assoc, ← C_mul]
  · rintro ⟨c, hc⟩
    obtain ⟨⟨a, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors R) c
    simp only at hcs
    refine ⟨s, nonZeroDivisors.ne_zero s.2, Submodule.mem_span_singleton.2 ⟨a, Subtype.ext ?_⟩⟩
    change a • (X : K[X]) = (s : R) • (b : K[X])
    rw [hc, Algebra.smul_def, Algebra.smul_def, Polynomial.algebraMap_apply,
      Polynomial.algebraMap_apply, ← mul_assoc, ← C_mul, mul_comm (algebraMap R K s), hcs]

/-- **`K · T` is not a finitely generated `R`-module**: otherwise `K` would be finite over
`R`, hence integral, and `ϖ⁻¹ ∈ K` would lie in `R`. -/
theorem not_fg_saturation : ¬ (KT R K).FG := by
  intro h
  -- the coefficient of `T` maps `K · T` onto `K`
  let φ : B R K →ₗ[R] K :=
    { toFun := fun b => (b : K[X]).coeff 1
      map_add' := fun _ _ => by simp
      map_smul' := fun r b => by
        simp [Algebra.smul_def, Polynomial.algebraMap_apply, coeff_C_mul] }
  have hφ : (KT R K).map φ = ⊤ := by
    refine eq_top_iff.2 fun c _ => ⟨⟨C c * X, C_mul_X_mem c⟩, ⟨c, rfl⟩, by simp [φ]⟩
  have : Module.Finite R K := ⟨hφ ▸ h.map φ⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ0 : algebraMap R K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hϖ.ne_zero
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.IsIntegral.isIntegral (R := R) (algebraMap R K ϖ)⁻¹)
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one y (IsFractionRing.injective R K ?_)
  rw [map_mul, hy, mul_inv_cancel₀ hϖ0, map_one]

/-! ### The commutative-algebra core of the edition's argument for page 9

For an element `π` of a commutative ring `A`, write `d(A) = ⋂ₙ πⁿA`. -/

section Components

variable {A : Type*} [CommRing A] (π : A)

/-- **A component missing the special fibre gives `d(A) ≠ 0`.** If a minimal prime `𝔭`
satisfies `𝔭 + πA = A`, write `1 - cπ ∈ 𝔭`; it is a zero divisor, say `a(1 - cπ) = 0`
with `a ≠ 0`, and then `a = a(cπ)ⁿ ∈ πⁿA` for all `n`. -/
theorem iInf_pow_ne_bot_of_minimalPrime {p : Ideal A} (hp : p ∈ minimalPrimes A)
    (h : p ⊔ Ideal.span {π} = ⊤) : ⨅ n : ℕ, Ideal.span {π} ^ n ≠ ⊥ := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : A)))
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨a, hay, ha⟩ : ∃ a, a * y = 0 ∧ a ≠ 0 := by
    simpa [mem_nonZeroDivisors_iff_right] using
      Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp) hy
  have h1 : a * (c * π) = a := by linear_combination a * hyz - hay
  have hn (n : ℕ) : a * (c * π) ^ n = a := by induction n <;> simp_all [pow_succ', ← mul_assoc]
  refine fun hbot => ha (Ideal.mem_bot.1 (hbot ▸ Ideal.mem_iInf.2 fun n => ?_))
  exact Ideal.span_singleton_pow π n ▸
    Ideal.mem_span_singleton'.2 ⟨a * c ^ n, by rw [mul_assoc, ← mul_pow, hn]⟩

/-- **Components meeting the special fibre give `d(A) = 0`, for `A` reduced and Noetherian.**
For a minimal prime `𝔭`, `A/𝔭` is a Noetherian domain in which `π` generates a proper ideal,
so `⋂ₙ πⁿ(A/𝔭) = 0` by Krull's intersection theorem: `d(A) ⊆ 𝔭`. The intersection of the
minimal primes is the nilradical, which is `0`. -/
theorem iInf_pow_eq_bot_of_minimalPrimes [IsNoetherianRing A] [IsReduced A]
    (h : ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤) :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  rw [← Ideal.radical_bot_of_isReduced, ← Ideal.sInf_minimalPrimes]
  refine Ideal.mem_sInf.2 fun p hp => have := hp.isPrime; ?_
  let f := Ideal.Quotient.mk p
  have hI : (Ideal.span {π}).map f ≠ ⊤ := fun hI => h p hp (by
    simpa [f, Ideal.comap_map_of_surjective' f Ideal.Quotient.mk_surjective, sup_comm] using
      congrArg (Ideal.comap f) hI)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isDomain _ hI]
  exact Ideal.mem_iInf.2 fun n => Ideal.map_pow f _ n ▸ Ideal.mem_map_of_mem f
    (Ideal.mem_iInf.1 hx n)

/-- **The criterion for `A` reduced and Noetherian**: `⋂ₙ πⁿA = 0` if and only if every
irreducible component of `Spec A` meets the special fibre `V(π)`. -/
theorem iInf_pow_eq_bot_iff [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ :=
  ⟨fun h0 _ hp h => iInf_pow_ne_bot_of_minimalPrime π hp h h0,
    iInf_pow_eq_bot_of_minimalPrimes π⟩

end Components

end Grothendieck.Folder90
