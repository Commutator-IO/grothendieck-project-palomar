module

public import Mathlib

@[expose] public section


/-!
# Folder 101, pages 10–11: local duality in dimension one for every `O_X`-module

The modernised reading `transcripts/101/101.modern.tex` (« Dimensions 0 et 1 : la dualité
tient ») follows pages 10 and 11: for `A` a complete discrete valuation ring with fraction field
`K` and `X = Spec A`, an `O_X`-module, quasi-coherent or not, is a triple `(M₀, M₁, u)` — an
`A`-module `M₀`, a `K`-vector space `M₁` and an `A`-linear `u : M₀ → M₁` — with
`H⁰_x(F) = Ker u` and `H¹_x(F) = Coker u`; the injective resolution `O_X → K_X → K_X/O_X`
gives `Ext^•(X; F, O_X)` as the cohomology of `Hom_K(M₁, K) → Hom_A(M₀, K/A)`,
`g ↦ g ∘ u mod A`, and the duality maps become `Ext⁰ → Hom_A(Coker u, K/A)` and
`Ext¹ → Hom_A(Ker u, K/A)`. The page proves them bijective by three facts a), b), c). This is
the reachable part of finding `101-sheaf-duality-dim-one` of `src/content/findings.ts`, in the
page's own model: the equivalence between `O_X`-modules and triples, and the computation of
`Ext` by that resolution, are the page's reduction and are not formalised.

* `eq_zero_of_mem`, fact a): a `K`-linear map with values in `A` is zero.
* `lift_K`, fact b): `A` being complete, every `A`-linear `K → K/A` is the reduction of
  `x ↦ c x` for some `c ∈ K` (`Hom_A(K, K/A) = K̂ = K`, hence `Ext¹_A(K, A) = 0`); `lift_vs`
  extends this to `A`-linear maps from any `K`-vector space, through a basis.
* `baer_KA`, fact c): `K/A` is an injective `A`-module (Baer's criterion).
* `duality_dim_one`: the two duality maps `phi0 : Ext⁰ → Hom_A(Coker u, K/A)` and
  `phi1 : Ext¹ → Hom_A(Ker u, K/A)` are bijective for every triple.

`Ext0` is the kernel and `Ext1` the cokernel (by `imD`) of `g ↦ g ∘ u mod A`.
-/

namespace Grothendieck.Folder101

open IsLocalRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- `A` inside its fraction field `K`. -/
abbrev Aₖ : Submodule A K := LinearMap.range (Algebra.linearMap A K)

/-- `K/A = H¹_x(O_X)`, the module `I` of the page. -/
abbrev KA := K ⧸ Aₖ A K

variable {A K}

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
lemma mem_Aₖ {x : K} : x ∈ Aₖ A K ↔ ∃ a : A, algebraMap A K a = x := Iff.rfl

/-- Fact a) of page 11: a `K`-linear map with values in `A` is zero. -/
theorem eq_zero_of_mem {M : Type*} [AddCommGroup M] [Module K M] (g : M →ₗ[K] K)
    (hg : ∀ m, g m ∈ Aₖ A K) : g = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hp : algebraMap A K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hϖ.ne_zero
  ext m
  by_contra hm
  obtain ⟨a, ha⟩ := hg (((algebraMap A K ϖ)⁻¹ * (g m)⁻¹) • m)
  rw [Algebra.linearMap_apply, map_smul, smul_eq_mul, mul_assoc,
    inv_mul_cancel₀ (by simpa using hm), mul_one] at ha
  exact hϖ.not_isUnit (.of_mul_eq_one a (IsFractionRing.injective A K
    (by rw [map_mul, ha, map_one, mul_inv_cancel₀ hp])))

/-- Every element of `K` is `a / ϖⁿ` with `a ∈ A`. -/
lemma exists_eq_div_pow {ϖ : A} (hϖ : Irreducible ϖ) (x : K) :
    ∃ (a : A) (n : ℕ), x = algebraMap A K a * ((algebraMap A K ϖ) ^ n)⁻¹ := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨a * ↑v⁻¹, n, ?_⟩
  rw [hv, map_mul, map_mul, map_pow, map_units_inv, div_eq_mul_inv, mul_inv]
  ring

section Complete

variable [IsAdicComplete (maximalIdeal A) A]

/-- Fact b) of page 11: `A` being complete, every `A`-linear map `K → K/A` lifts to `K → K`;
it is reduction of a multiplication `x ↦ c x` (`Hom_A(K, K/A) = K̂ = K`). -/
theorem lift_K (f : K →ₗ[A] KA A K) :
    ∃ c : K, ∀ x, f x = Submodule.Quotient.mk (c * x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set p := algebraMap A K ϖ with hpdef
  have hp : p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hϖ.ne_zero
  choose c hc using fun n : ℕ => Submodule.Quotient.mk_surjective (Aₖ A K) (f (p ^ n)⁻¹)
  have step : ∀ n, ∃ s : A, algebraMap A K s = p * c (n + 1) - c n := fun n => by
    rw [← mem_Aₖ, ← Submodule.Quotient.eq,
      show p * c (n + 1) = ϖ • c (n + 1) from (Algebra.smul_def ϖ _).symm,
      Submodule.Quotient.mk_smul, hc, hc, ← map_smul, Algebra.smul_def, ← hpdef]
    congr 1
    rw [pow_succ, mul_inv, mul_left_comm, mul_inv_cancel₀ hp, mul_one]
  choose s hs using step
  set d : ℕ → K := fun n => p ^ n * c n with hd
  have hdiff : ∀ n, d (n + 1) - d n = algebraMap A K (ϖ ^ n * s n) := fun n => by
    simp only [hd, map_mul, map_pow, hs, ← hpdef]; ring
  have hmem : ∀ n, ∃ e : A, algebraMap A K e = d n - d 0 := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      exact ⟨e + ϖ ^ n * s n, by rw [map_add, he, ← hdiff]; ring⟩
  choose e he using hmem
  have he_succ : ∀ n, e (n + 1) - e n = ϖ ^ n * s n := fun n =>
    IsFractionRing.injective A K (by rw [map_sub, he, he, ← hdiff]; ring)
  have hcauchy : ∀ m k, e (m + k) - e m ∈ Ideal.span {ϖ ^ m} := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have : e (m + (k + 1)) - e m = (e (m + k) - e m) + ϖ ^ m * (ϖ ^ k * s (m + k)) := by
        rw [← mul_assoc, ← pow_add, ← he_succ, ← add_assoc]; ring
      rw [this]
      exact Ideal.add_mem _ ih (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hI : ∀ n, (maximalIdeal A ^ n • ⊤ : Submodule A A) = Ideal.span {ϖ ^ n} := fun n => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (maximalIdeal A) A)
    (f := e) (by
      intro m n hmn
      rw [hI, SModEq.sub_mem]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 (hcauchy m k))
  refine ⟨d 0 + algebraMap A K L, fun x => ?_⟩
  obtain ⟨a, n, rfl⟩ := exists_eq_div_pow hϖ x
  have hn := hL n
  rw [hI, SModEq.sub_mem, Ideal.mem_span_singleton'] at hn
  obtain ⟨t, ht⟩ := hn
  have hfx : f (algebraMap A K a * (p ^ n)⁻¹) =
      Submodule.Quotient.mk (algebraMap A K a * c n) := by
    rw [← Algebra.smul_def, map_smul, ← hc, ← Submodule.Quotient.mk_smul, Algebra.smul_def]
  rw [hfx, Submodule.Quotient.eq]
  refine ⟨a * t, ?_⟩
  have hen : algebraMap A K (e n) = algebraMap A K L + algebraMap A K t * p ^ n := by
    have := congrArg (algebraMap A K) ht
    rw [map_mul, map_pow, map_sub] at this
    linear_combination -this
  have hcn : c n = (d 0 + algebraMap A K (e n)) * (p ^ n)⁻¹ := by
    rw [he]; simp only [hd]; field_simp; ring
  simp only [Algebra.linearMap_apply, map_mul]
  rw [hcn, hen]
  simp only [← hpdef]
  field_simp
  ring

/-- Every `A`-linear map from a `K`-vector space to `K/A` lifts to a `K`-linear map to `K`
(fact b) applied on a basis). -/
theorem lift_vs {M : Type*} [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M]
    (h : M →ₗ[A] KA A K) : ∃ g : M →ₗ[K] K, ∀ m, Submodule.Quotient.mk (g m) = h m := by
  classical
  let b := Module.Basis.ofVectorSpace K M
  choose c hc using fun i =>
    lift_K (h ∘ₗ ((LinearMap.toSpanSingleton K M (b i)).restrictScalars A))
  refine ⟨b.constr K c, fun m => ?_⟩
  change (Aₖ A K).mkQ (b.constr K c m) = h m
  rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hc i (b.repr m i)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearMap.toSpanSingleton_apply] at this
  rw [this, map_smul, Module.Basis.constr_basis, Submodule.mkQ_apply, smul_eq_mul, mul_comm]

end Complete

/-- Fact c) of page 11: `K/A` is an injective `A`-module (Baer's criterion; `A` is principal
and `K/A` divisible). -/
theorem baer_KA : Module.Baer A (KA A K) := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  rcases eq_or_ne a 0 with rfl | ha
  · refine ⟨0, fun x hx => ?_⟩
    obtain rfl : x = 0 := by simpa using hx
    exact (map_zero g).symm.trans (congrArg g (Subtype.ext rfl))
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (Aₖ A K)
    (g ⟨a, Ideal.mem_span_singleton_self a⟩)
  have hpa : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha
  refine ⟨LinearMap.toSpanSingleton A _ (Submodule.Quotient.mk (y / algebraMap A K a)),
    fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [LinearMap.toSpanSingleton_apply, mul_smul, ← Submodule.Quotient.mk_smul,
    Algebra.smul_def, mul_div_cancel₀ _ hpa, hy, ← map_smul]
  rfl

/-! ## The page's model: triples `(M₀, M₁, u)` -/

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
  refine ⟨⟨fun g g' hgg => ?_, fun ψ => ?_⟩, ⟨?_, ?_⟩⟩
  · -- a): injectivity on `Ext⁰`
    have : g.1 - g'.1 = 0 := eq_zero_of_mem _ fun y => by
      simpa [phi0, Submodule.Quotient.eq] using LinearMap.congr_fun hgg (Submodule.Quotient.mk y)
    exact Subtype.ext (sub_eq_zero.1 this)
  · -- b): surjectivity on `Ext⁰`
    obtain ⟨g, hg⟩ := lift_vs (ψ ∘ₗ (LinearMap.range u).mkQ)
    refine ⟨⟨g, fun m => ?_⟩, ?_⟩
    · rw [← Submodule.Quotient.mk_eq_zero, hg]
      simp [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self u m)]
    · refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
      simp [phi0, hg]
  · -- c), second half: injectivity on `Ext¹`
    rw [← LinearMap.ker_eq_bot, phi1]
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun h hh => ?_
    rw [LinearMap.mem_ker] at hh
    have hk : LinearMap.ker u ≤ LinearMap.ker h := fun m hm => by
      simpa using LinearMap.congr_fun hh ⟨m, hm⟩
    have hinj : Function.Injective ((LinearMap.ker u).liftQ u le_rfl) :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
    obtain ⟨H, hH⟩ := baer_KA.extension_property _ hinj ((LinearMap.ker u).liftQ h hk)
    obtain ⟨g, hg⟩ := lift_vs (A := A) H
    refine ⟨g, fun m => ?_⟩
    rw [hg]
    simpa using (LinearMap.congr_fun hH (Submodule.Quotient.mk m)).symm
  · -- c): surjectivity on `Ext¹`
    intro k
    obtain ⟨H, hH⟩ := baer_KA.extension_property (LinearMap.ker u).subtype
      (Submodule.subtype_injective _) k
    refine ⟨Submodule.Quotient.mk H, ?_⟩
    ext x
    rw [← hH]
    simp [phi1]

/-! ## The converse: `Ext¹_A(K, A) = 0` forces completeness -/

/-- **Converse of fact b)**: if every `A`-linear map `K → K/A` lifts to an `A`-linear map
`K → K` (that is, `Hom_A(K, K) → Hom_A(K, K/A)` is onto, i.e. `Ext¹_A(K, A) = 0`, `K` being
injective), then `A` is complete. A Cauchy sequence `(eₙ)` gives `f : K → K/A`,
`x ↦ eₙ x mod A` for any `n` with `ϖⁿ x ∈ A`; a lift `g` of `f` has limit `g 1`. -/
theorem isAdicComplete_of_lift
    (H : ∀ f : K →ₗ[A] KA A K, ∃ g : K →ₗ[A] K, ∀ x, Submodule.Quotient.mk (g x) = f x) :
    IsAdicComplete (maximalIdeal A) A := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set p := algebraMap A K ϖ with hpdef
  have hp : p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hϖ.ne_zero
  have hI : ∀ n, (maximalIdeal A ^ n • ⊤ : Submodule A A) = Ideal.span {ϖ ^ n} := fun n => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  refine { prec' := fun e he => ?_ }
  simp only [hI, SModEq.sub_mem, Ideal.mem_span_singleton'] at he ⊢
  -- every `x` has some `n` with `ϖⁿ x ∈ A`
  choose N hNx using fun x : K => show ∃ n, p ^ n * x ∈ Aₖ A K by
    obtain ⟨a, n, rfl⟩ := exists_eq_div_pow hϖ x
    exact ⟨n, a, by simp [hp, ← hpdef, mul_left_comm]⟩
  set E : ℕ → K := fun n => algebraMap A K (e n) with hE
  -- independence of `n`
  have key : ∀ x n, p ^ n * x ∈ Aₖ A K → ∀ m, n ≤ m → E m * x - E n * x ∈ Aₖ A K := by
    rintro x n ⟨b, hb⟩ m hnm
    obtain ⟨t, ht⟩ := he hnm
    refine ⟨-(t * b), ?_⟩
    have := congrArg (algebraMap A K) ht
    simp only [hE, Algebra.linearMap_apply, map_mul, map_pow, map_sub, map_neg, ← hpdef] at *
    linear_combination (-x) * this - algebraMap A K t * hb
  have well : ∀ x n, p ^ n * x ∈ Aₖ A K →
      (Submodule.Quotient.mk (E (N x) * x) : KA A K) = Submodule.Quotient.mk (E n * x) :=
    fun x n hn => by
    rw [Submodule.Quotient.eq]
    convert (Aₖ A K).sub_mem (key x n hn _ (le_max_left _ (N x)))
      (key x _ (hNx x) _ (le_max_right n _)) using 1; ring
  have mono : ∀ x n m, p ^ n * x ∈ Aₖ A K → n ≤ m → p ^ m * x ∈ Aₖ A K := by
    rintro x n m hn hnm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    convert (Aₖ A K).smul_mem (ϖ ^ k) hn using 1
    rw [Algebra.smul_def, map_pow, ← hpdef]; ring
  let f : K →ₗ[A] KA A K :=
    { toFun := fun x => Submodule.Quotient.mk (E (N x) * x)
      map_add' := fun x y => by
        have hx := mono x _ (N x + N y + N (x + y)) (hNx x) (by omega)
        have hy := mono y _ (N x + N y + N (x + y)) (hNx y) (by omega)
        rw [well x _ hx, well y _ hy, well (x + y) _ (by rw [mul_add]; exact add_mem hx hy),
          ← Submodule.Quotient.mk_add, mul_add]
      map_smul' := fun a x => by
        rw [well (a • x) (N x) (by rw [mul_smul_comm]; exact (Aₖ A K).smul_mem a (hNx x)),
          RingHom.id_apply, ← Submodule.Quotient.mk_smul, mul_smul_comm] }
  have hf : ∀ x n, p ^ n * x ∈ Aₖ A K → f x = Submodule.Quotient.mk (E n * x) := well
  obtain ⟨g, hg⟩ := H f
  obtain ⟨L, hL⟩ : g 1 - E 0 ∈ Aₖ A K := by
    rw [← Submodule.Quotient.eq, hg, hf 1 0 ⟨1, by simp⟩, mul_one]
  refine ⟨L + e 0, fun n => ?_⟩
  obtain ⟨a, ha⟩ : g (p ^ n)⁻¹ - E n * (p ^ n)⁻¹ ∈ Aₖ A K := by
    rw [← Submodule.Quotient.eq, hg, hf _ n ⟨1, by simp [hp]⟩]
  have h1 : g 1 = p ^ n * g (p ^ n)⁻¹ := by
    rw [← map_pow, ← Algebra.smul_def, ← map_smul, Algebra.smul_def, map_pow, ← hpdef,
      mul_inv_cancel₀ (pow_ne_zero _ hp)]
  refine ⟨-a, IsFractionRing.injective A K ?_⟩
  simp only [Algebra.linearMap_apply] at hL ha
  simp only [map_mul, map_neg, map_pow, map_sub, map_add, ← hpdef, hL, h1, ha, hE]
  field_simp
  ring

/-- For a discrete valuation ring, completeness is equivalent to `Ext¹_A(K, A) = 0`, in the form
« every `A`-linear `K → K/A` lifts to `K` » (`lift_K` and `isAdicComplete_of_lift`). -/
theorem isAdicComplete_iff_lift : IsAdicComplete (maximalIdeal A) A ↔
    ∀ f : K →ₗ[A] KA A K, ∃ g : K →ₗ[A] K, ∀ x, Submodule.Quotient.mk (g x) = f x :=
  ⟨fun _ f => let ⟨c, hc⟩ := lift_K f; ⟨LinearMap.mulLeft A c, fun x => (hc x).symm⟩,
    isAdicComplete_of_lift⟩

end Grothendieck.Folder101
