module

public import Mathlib

@[expose] public section


/-!
# Folder 100, pages 36–38: points of dimension one avoiding countably many divisors

The modernised reading `transcripts/100/100.modern.tex` (« Un argument de Baire ») gives the
Corollary of page 38: in an integral complete local scheme, countably many nowhere-dense closed
subsets miss some point of dimension one. The proof reduces to `Θ = V⟦T₁, …, Tₙ⟧`, `V` a complete
discrete valuation ring, parametrises the `V`-homomorphisms `Θ → V` by `𝔪ⁿ` and concludes by
Baire. This file proves the case `n = 1`, `Θ = V⟦T⟧` of dimension `2`, which is the reachable
part of finding `100-baire-dimension-one-points` of `src/content/findings.ts`.

* `quotEquiv`: for `a ∈ 𝔪`, `V⟦T⟧ ⧸ (T − a) ≃ V` (`T − a` is a distinguished polynomial, so the
  quotient is `V[T] ⧸ (T − a)`); the kernel `(T − a)` of `T ↦ a` is a point of dimension one.
* `exists_poly_mul_unit`: a nonzero `f ∈ V⟦T⟧` is `Q · u` with `Q` a nonzero polynomial and `u`
  a unit — `f = ϖ^v g` with `g` of unit content (`exists_content`), then Weierstrass
  preparation for `g`.
* `finite_bad`: `f ∈ (T − a)` iff `Q(a) = 0`, so only finitely many `a` are bad for `f ≠ 0`.
* `uncountable`: a complete discrete valuation ring is uncountable (the series
  `∑ εᵢ ϖⁱ`, `εᵢ ∈ {0, 1}`, are pairwise distinct).
* `exists_avoid`: for countably many nonzero `fᵢ ∈ V⟦T⟧` there is `a ∈ 𝔪` with `fᵢ ∉ (T − a)`
  for every `i`. Countability of the bad set replaces Baire: each `fᵢ` excludes finitely many
  `a`, and `𝔪 = ϖV` is uncountable.

Not formalised: the case of several variables, where the bad set of one `f` is no longer
finite and Baire is needed; the reduction of a complete local domain to a finite extension of
`V⟦T₁, …, Tₙ⟧` (Cohen) and the lifting of points along it; the Proposition of page 36.
-/

namespace Grothendieck.Folder100

open IsLocalRing
open scoped Polynomial PowerSeries

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/-- `T − a`, for `a ∈ 𝔪`, is distinguished. -/
lemma isDistinguishedAt {a : V} (ha : a ∈ maximalIdeal V) :
    (Polynomial.X - Polynomial.C a).IsDistinguishedAt (maximalIdeal V) where
  mem {n} hn := by
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hn
    subst hn
    simpa using ha
  monic := Polynomial.monic_X_sub_C a

omit [IsDomain V] [IsDiscreteValuationRing V] in
lemma coe_X_sub_C (a : V) :
    ((Polynomial.X - Polynomial.C a : V[X]) : V⟦X⟧) = PowerSeries.X - PowerSeries.C a := by
  simp

variable [IsAdicComplete (maximalIdeal V) V]

/-- `V⟦T⟧ ⧸ (T − a) ≃ V` for `a ∈ 𝔪`. -/
noncomputable def quotEquiv {a : V} (ha : a ∈ maximalIdeal V) :
    (V⟦X⟧ ⧸ Ideal.span {PowerSeries.X - PowerSeries.C a}) ≃ₐ[V] V :=
  (Ideal.quotientEquivAlgOfEq V (by rw [coe_X_sub_C])).trans
    ((isDistinguishedAt ha).algEquivQuotient.symm.trans (Polynomial.quotientSpanXSubCAlgEquiv a))

/-- A polynomial lies in `(T − a) ⊂ V⟦T⟧` iff it vanishes at `a`. -/
lemma coe_mem_iff {a : V} (ha : a ∈ maximalIdeal V) (Q : V[X]) :
    (Q : V⟦X⟧) ∈ Ideal.span {PowerSeries.X - PowerSeries.C a} ↔ Q.IsRoot a := by
  have e : (isDistinguishedAt ha).algEquivQuotient (Ideal.Quotient.mk _ Q) =
      Ideal.Quotient.mk _ (Q : V⟦X⟧) := rfl
  rw [← coe_X_sub_C, ← Ideal.Quotient.eq_zero_iff_mem, ← e,
    map_eq_zero_iff _ (AlgEquiv.injective _),
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]

omit [IsAdicComplete (maximalIdeal V) V] in
/-- The content: a nonzero `f` is `ϖ^v g` with `g` not zero modulo `𝔪`. -/
lemma exists_content {ϖ : V} (hϖ : Irreducible ϖ) {f : V⟦X⟧} (hf : f ≠ 0) :
    ∃ (v : ℕ) (g : V⟦X⟧), f = PowerSeries.C (ϖ ^ v) * g ∧ g.map (residue V) ≠ 0 := by
  have hex : ∃ v k, ¬ ϖ ^ (v + 1) ∣ PowerSeries.coeff k f := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k f ≠ 0 := by
      by_contra! h
      exact hf (PowerSeries.ext fun n => by simpa using h n)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk hϖ
    refine ⟨n, k, fun h => hϖ.not_isUnit ?_⟩
    rw [hu, pow_succ, mul_comm (u : V), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)] at h
    exact isUnit_of_dvd_unit h u.isUnit
  classical
  have hdvd : ∀ k, ϖ ^ Nat.find hex ∣ PowerSeries.coeff k f := by
    intro k
    rcases h : Nat.find hex with _ | w
    · simp
    · by_contra hk
      exact Nat.find_min hex (h ▸ Nat.lt_succ_self w) ⟨k, hk⟩
  choose c hc using hdvd
  obtain ⟨k, hk⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, PowerSeries.mk c, PowerSeries.ext fun n => by
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc], fun h0 => ?_⟩
  have h1 := congrArg (PowerSeries.coeff k) h0
  rw [PowerSeries.coeff_map, map_zero, residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton,
    PowerSeries.coeff_mk] at h1
  exact hk (by rw [hc k, pow_succ]; exact mul_dvd_mul_left _ h1)

/-- A nonzero `f ∈ V⟦T⟧` is a nonzero polynomial times a unit. -/
theorem exists_poly_mul_unit {f : V⟦X⟧} (hf : f ≠ 0) :
    ∃ (Q : V[X]) (u : V⟦X⟧), Q ≠ 0 ∧ IsUnit u ∧ f = Q * u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, g, rfl, hg⟩ := exists_content hϖ hf
  obtain ⟨P, u, H⟩ := g.exists_isWeierstrassFactorization hg
  refine ⟨Polynomial.C (ϖ ^ v) * P, u, mul_ne_zero (by simpa using pow_ne_zero v hϖ.ne_zero)
    H.isDistinguishedAt.monic.ne_zero, H.isUnit, ?_⟩
  rw [H.eq_mul, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc]

/-- A nonzero `f` lies in `(T − a)` for finitely many `a ∈ 𝔪` only. -/
theorem finite_bad {f : V⟦X⟧} (hf : f ≠ 0) :
    {a | a ∈ maximalIdeal V ∧ f ∈ Ideal.span {PowerSeries.X - PowerSeries.C a}}.Finite := by
  obtain ⟨Q, u, hQ, hu, rfl⟩ := exists_poly_mul_unit hf
  refine (Polynomial.finite_setOfPred_isRoot hQ).subset fun a ⟨ha, hm⟩ => (coe_mem_iff ha Q).1 ?_
  simpa [Ideal.mul_unit_mem_iff_mem _ hu] using hm

/-- The partial sums `∑_{i < n} εᵢ ϖⁱ`. -/
def psum (ϖ : V) (ε : ℕ → Bool) (n : ℕ) : V := ∑ i ∈ Finset.range n, if ε i then ϖ ^ i else 0

/-- A complete discrete valuation ring is uncountable: `ε ↦ ∑ εᵢ ϖⁱ` is injective on
`{0, 1}^ℕ`. -/
theorem uncountable : Uncountable V := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : ∀ n : ℕ, maximalIdeal V ^ n = Ideal.span {ϖ ^ n} := fun n => by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow]
  have hsm : ∀ (x y : V) n, x ≡ y [SMOD (maximalIdeal V ^ n • ⊤ : Submodule V V)] ↔
      ϖ ^ n ∣ x - y := fun x y n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hm, Ideal.mem_span_singleton]
  have hs : ∀ ε {m n : ℕ}, m ≤ n → ϖ ^ m ∣ psum ϖ ε n - psum ϖ ε m := fun ε m n hmn => by
    rw [psum, psum, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    exact Finset.dvd_sum fun i hi => by
      split_ifs
      · exact pow_dvd_pow ϖ (Finset.mem_Ico.1 hi).1
      · exact dvd_zero _
  have hL : ∀ ε, ∃ L, ∀ n, ϖ ^ n ∣ psum ϖ ε n - L := fun ε => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal V) inferInstance (f := psum ϖ ε)
      fun {m n} hmn => (hsm _ _ _).2 (by rw [← neg_sub, dvd_neg]; exact hs ε hmn)
    exact ⟨L, fun n => (hsm _ _ _).1 (hL n)⟩
  choose L hL using hL
  have hinj : Function.Injective L := fun ε ε' h => by
    by_contra hne
    have hex : ∃ j, ε j ≠ ε' j := not_forall.1 fun h' => hne (funext h')
    classical
    set j := Nat.find hex
    have hd : psum ϖ ε (j + 1) - psum ϖ ε' (j + 1) =
        (if ε j then ϖ ^ j else 0) - if ε' j then ϖ ^ j else 0 := by
      have hsum : ∑ i ∈ Finset.range j, (if ε i then ϖ ^ i else 0) =
          ∑ i ∈ Finset.range j, (if ε' i then ϖ ^ i else 0) :=
        Finset.sum_congr rfl fun i hi => by
          rw [not_not.1 (Nat.find_min hex (Finset.mem_range.1 hi))]
      simp only [psum, Finset.sum_range_succ, hsum]
      ring
    have h1 : ϖ ^ (j + 1) ∣ psum ϖ ε (j + 1) - psum ϖ ε' (j + 1) := by
      have := dvd_sub (hL ε (j + 1)) (hL ε' (j + 1))
      rwa [h, sub_sub_sub_cancel_right] at this
    have h2 : ϖ ^ (j + 1) ∣ ϖ ^ j := by
      have hj : ε j ≠ ε' j := Nat.find_spec hex
      rw [hd] at h1
      cases hε : ε j <;> cases hε' : ε' j <;> simp only [hε, hε'] at h1 hj <;>
        simp_all [dvd_neg]
    exact absurd ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h2) (by omega)
  have : Uncountable (ℕ → Bool) := by
    rw [← Cardinal.aleph0_lt_mk_iff, ← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat]
    exact Cardinal.cantor _
  exact hinj.uncountable

/-- The Corollary of page 38 for `Θ = V⟦T⟧`: for countably many nonzero `fᵢ ∈ V⟦T⟧` there is
`a ∈ 𝔪` with `fᵢ ∉ (T − a)` for every `i`; `V⟦T⟧ ⧸ (T − a) ≃ V` by `quotEquiv`, so `(T − a)` is
a point of dimension one outside every `V(fᵢ)`. -/
theorem exists_avoid {ι : Type*} [Countable ι] (f : ι → V⟦X⟧) (hf : ∀ i, f i ≠ 0) :
    ∃ a ∈ maximalIdeal V, ∀ i, f i ∉ Ideal.span {PowerSeries.X - PowerSeries.C a} := by
  by_contra! h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hc : (⋃ i, {a | a ∈ maximalIdeal V ∧
      f i ∈ Ideal.span {PowerSeries.X - PowerSeries.C a}}).Countable :=
    Set.countable_iUnion fun i => (finite_bad (hf i)).countable
  have hϖm : ϖ ∈ maximalIdeal V := hϖ.not_isUnit
  have : Countable V := by
    have := hc.to_subtype
    refine Function.Injective.countable (f := fun x : V => (⟨ϖ * x, ?_⟩ : ↥(⋃ i, {a |
      a ∈ maximalIdeal V ∧ f i ∈ Ideal.span {PowerSeries.X - PowerSeries.C a}}))) ?_
    · obtain ⟨i, hi⟩ := h (ϖ * x) (Ideal.mul_mem_right x _ hϖm)
      exact Set.mem_iUnion.2 ⟨i, Ideal.mul_mem_right x _ hϖm, hi⟩
    · intro x y hxy
      exact mul_left_cancel₀ hϖ.ne_zero (congrArg Subtype.val hxy)
  have hu : Uncountable V := uncountable
  exact not_countable this

end Grothendieck.Folder100

/-!
## The Proposition of page 36 and the Corollary of page 38, in every dimension

The page's proof goes through Cohen's structure theorem and Baire on `𝔪ⁿ`; neither is needed.
The completeness of `R` enters once, through **countable prime avoidance** (Burch): the maximal
ideal of a complete noetherian local ring is not contained in a countable union of primes
`≠ 𝔪` (`exists_mem_maximalIdeal_notMem_of_countable`). The point avoiding them is the limit of
a sequence built step by step — Baire's argument made explicit — and each step uses only that
primes are closed for the `𝔪`-adic topology (Krull's intersection theorem,
`exists_notMem_sup_pow`).

* `exists_isPrime_gt`: over a prime `P` with a chain `P < a < b`, countably many ideals
  `Iᵢ ⊄ P` leave a prime `Q > P` containing none of them. Otherwise every prime minimal over
  some `P + (x)`, `x ∈ 𝔪 ∖ P`, which is `≠ 𝔪` and has nothing strictly between it and `P`
  (Krull's principal ideal theorem, `not_chain_of_mem_minimalPrimes`), is minimal over some
  `P + Iᵢ`, and `𝔪` lies in the countable union of these primes.
* `exists_finite_subcover`, `exists_finite_subcover_of_countable`: the Proposition of page 36,
  with completeness restored. A minimal prime outside every `Zᵢ` exists unless finitely many
  `Zᵢ` cover; from it, `exists_isPrime_gt` climbs, lowering the coheight, to a point of
  coheight `≤ 1` outside every `Zᵢ`.
* `exists_coheight_eq_one`: the Corollary of page 38, for proper closed subsets (in the
  irreducible `Spec R`, the rare closed subsets are the proper ones).

`dim closure {x}` is read as the coheight of `x` in the poset `Spec R`, the supremum of the
lengths of chains of primes starting at `x`, which is the Krull dimension of `R ⧸ x`.
-/
namespace Grothendieck.Folder100.Baire

open IsLocalRing PrimeSpectrum

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Primes are closed (Krull): if `x ∉ p` then `x ∉ p + 𝔪ᴺ` for some `N`. -/
lemma exists_notMem_sup_pow {p : Ideal R} (hp : p ≠ ⊤) {x : R} (hx : x ∉ p) :
    ∃ N : ℕ, x ∉ p ⊔ maximalIdeal R ^ N := by
  have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p) := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [sup_eq_left.mpr (le_maximalIdeal hp)]
  by_contra! h
  have h0 : Ideal.Quotient.mk p x ∈ ⨅ n : ℕ, maximalIdeal (R ⧸ p) ^ n := by
    rw [Ideal.mem_iInf]
    intro N
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk p) (h N)
    rwa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, hm] at this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at h0
  exact hx h0

/-- The invariant of the construction: `x` stays off `f j + 𝔪ᴺ` for `j < k`. -/
def Good (f : ℕ → Ideal R) (k : ℕ) (x : R) (N : ℕ) : Prop :=
  ∀ j < k, x ∉ f j ⊔ maximalIdeal R ^ N

lemma step {f : ℕ → Ideal R} (hf : ∀ j, (f j).IsPrime) (hfm : ∀ j, f j ≠ maximalIdeal R)
    (k : ℕ) (x : R) (N : ℕ) (h : Good f k x N) :
    ∃ q : R × ℕ, Good f (k + 1) q.1 q.2 ∧ q.1 - x ∈ maximalIdeal R ^ N ∧ N < q.2 := by
  obtain ⟨x', hx'k, hx'⟩ : ∃ x', x' ∉ f k ∧ x' - x ∈ maximalIdeal R ^ N := by
    by_cases hxk : x ∈ f k
    · have : ¬ maximalIdeal R ^ N ≤ f k := fun hle =>
        hfm k (le_antisymm (le_maximalIdeal (hf k).ne_top) ((hf k).le_of_pow_le hle))
      obtain ⟨y, hy, hyk⟩ := Set.not_subset.1 this
      exact ⟨x + y, fun h' => hyk (by simpa using sub_mem h' hxk), by simpa using hy⟩
    · exact ⟨x, hxk, by simp⟩
  obtain ⟨M, hM⟩ := exists_notMem_sup_pow (hf k).ne_top hx'k
  refine ⟨(x', max (N + 1) M), fun j hj => ?_, hx', by omega⟩
  have hle : maximalIdeal R ^ max (N + 1) M ≤ maximalIdeal R ^ N :=
    Ideal.pow_le_pow_right (by omega)
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · intro hmem
    apply h j hj
    rw [← sub_sub_cancel x' x]
    exact sub_mem (sup_le_sup_left hle _ hmem) (Ideal.mem_sup_right hx')
  · have hle' : maximalIdeal R ^ max (N + 1) M ≤ maximalIdeal R ^ M :=
      Ideal.pow_le_pow_right (le_max_right _ _)
    exact fun hmem => hM (sup_le_sup_left hle' _ hmem)

/-- The sequence of the construction, with its invariant. -/
noncomputable def seq {f : ℕ → Ideal R} (hf : ∀ j, (f j).IsPrime)
    (hfm : ∀ j, f j ≠ maximalIdeal R) : (k : ℕ) → {q : R × ℕ // Good f k q.1 q.2}
  | 0 => ⟨(0, 1), fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | k + 1 => ⟨Classical.choose (step hf hfm k _ _ (seq hf hfm k).2),
      (Classical.choose_spec (step hf hfm k _ _ (seq hf hfm k).2)).1⟩

variable [IsAdicComplete (maximalIdeal R) R]

/-- **Countable prime avoidance** (Burch): in a complete noetherian local ring, the maximal
ideal is not contained in the union of countably many primes different from it. -/
theorem exists_mem_maximalIdeal_forall_notMem (f : ℕ → Ideal R) (hf : ∀ j, (f j).IsPrime)
    (hfm : ∀ j, f j ≠ maximalIdeal R) : ∃ x ∈ maximalIdeal R, ∀ j, x ∉ f j := by
  let s := seq hf hfm
  let a : ℕ → R := fun k => (s k).1.1
  let N : ℕ → ℕ := fun k => (s k).1.2
  have hstep : ∀ k, a (k + 1) - a k ∈ maximalIdeal R ^ N k ∧ N k < N (k + 1) := fun k =>
    (Classical.choose_spec (step hf hfm k _ _ (s k).2)).2
  have hNmono : StrictMono N := strictMono_nat_of_lt_succ fun k => (hstep k).2
  have hN : ∀ k, k ≤ N k := fun k => hNmono.le_apply
  have hcauchy : ∀ k n, k ≤ n → a n - a k ∈ maximalIdeal R ^ N k := by
    intro k n hkn
    induction hkn with
    | refl => simp
    | step hle ih =>
      rename_i m
      rw [← sub_add_sub_cancel]
      exact add_mem (Ideal.pow_le_pow_right (hNmono.monotone hle) (hstep m).1) ih
  have hsm : ∀ n, (maximalIdeal R ^ n • ⊤ : Submodule R R) = maximalIdeal R ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal R) inferInstance (f := a)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact Ideal.pow_le_pow_right (hN m) (hcauchy m n hmn))
  have hLk : ∀ k, L - a k ∈ maximalIdeal R ^ N k := fun k => by
    have h2 := hL (N k)
    rw [SModEq.sub_mem, hsm] at h2
    rw [← sub_sub_sub_cancel_left (c := a (N k))]
    exact sub_mem (hcauchy k (N k) (hN k)) h2
  refine ⟨L, ?_, fun j hj => ?_⟩
  · simpa [a, N, s, seq] using hLk 0
  · apply (s (j + 1)).2 j (Nat.lt_succ_self j)
    show a (j + 1) ∈ f j ⊔ maximalIdeal R ^ N (j + 1)
    rw [← sub_sub_cancel L (a (j + 1))]
    exact sub_mem (Ideal.mem_sup_left hj) (Ideal.mem_sup_right (hLk _))

/-- Countable prime avoidance, for a countable set of primes. -/
theorem exists_mem_maximalIdeal_notMem_of_countable (S : Set (Ideal R)) (hS : S.Countable)
    (hSp : ∀ p ∈ S, p.IsPrime) (hSm : ∀ p ∈ S, p ≠ maximalIdeal R) :
    ∃ x ∈ maximalIdeal R, ∀ p ∈ S, x ∉ p := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
  obtain ⟨x, hx, hxf⟩ := exists_mem_maximalIdeal_forall_notMem f
    (fun j => hSp _ ⟨j, rfl⟩) (fun j => hSm _ ⟨j, rfl⟩)
  exact ⟨x, hx, by rintro _ ⟨j, rfl⟩; exact hxf j⟩

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] in
/-- Krull's principal ideal theorem over `P`: a prime minimal over `P + (x)` has no chain
`P < a < b` below it. -/
lemma not_chain_of_mem_minimalPrimes {P a b : Ideal R} [P.IsPrime] [a.IsPrime] [b.IsPrime]
    (hPa : P < a) (hab : a < b) {x : R} (hb : b ∈ (P ⊔ Ideal.span {x}).minimalPrimes) : False := by
  let φ := Ideal.Quotient.mk P
  have hsurj : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hb
  have hka : RingHom.ker φ ≤ a := by rw [Ideal.mk_ker]; exact hPa.le
  have hkb : RingHom.ker φ ≤ b := hka.trans hab.le
  have : (a.map φ).IsPrime := Ideal.map_isPrime_of_surjective hsurj hka
  have : (b.map φ).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkb
  have : (⊥ : Ideal (R ⧸ P)).IsPrime := Ideal.isPrime_bot
  have hlt : ∀ {c d : Ideal R}, P ≤ c → c < d → c.map φ < d.map φ := by
    intro c d hc hcd
    refine (Ideal.map_mono hcd.le).lt_of_not_ge fun e => hcd.not_ge ?_
    have := Ideal.comap_mono (f := φ) e
    rwa [Ideal.comap_map_of_surjective φ hsurj, Ideal.comap_map_of_surjective φ hsurj,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hc,
      sup_eq_left.mpr (hc.trans hcd.le)] at this
  have h0 : (⊥ : Ideal (R ⧸ P)) < a.map φ := by
    have := hlt le_rfl hPa
    rwa [Ideal.map_quotient_self] at this
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime (hlt hPa.le hab)
  have h2 : (1 : ℕ∞) + 1 ≤ 1 :=
    (add_le_add (le_add_self.trans e1) le_rfl).trans (e2.trans h1)
  exact absurd h2 (by decide)

/-- Over a prime `P` with a chain `P < a < b`, countably many ideals `Iᵢ ⊄ P` leave a prime
`Q > P` containing none of them: otherwise `𝔪` would lie in the countable union of the primes
`≠ 𝔪` minimal over the `P + Iᵢ` (Krull's principal ideal theorem), against countable prime
avoidance. -/
theorem exists_isPrime_gt (I : ℕ → Ideal R) {P : Ideal R} [P.IsPrime] (hI : ∀ i, ¬ I i ≤ P)
    {a b : Ideal R} [a.IsPrime] [b.IsPrime] (hPa : P < a) (hab : a < b) :
    ∃ Q : Ideal R, Q.IsPrime ∧ P < Q ∧ ∀ i, ¬ I i ≤ Q := by
  by_contra! H
  let S : Set (Ideal R) := {Q | Q ≠ maximalIdeal R ∧ ∃ i, Q ∈ (P ⊔ I i).minimalPrimes}
  have hS : S.Countable :=
    (Set.countable_iUnion fun i =>
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R (P ⊔ I i)).countable).mono
      fun Q ⟨_, i, hi⟩ => Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨x, hxm, hx⟩ := exists_mem_maximalIdeal_notMem_of_countable S hS
    (fun Q ⟨_, _, hi⟩ => hi.isPrime) fun Q h => h.1
  have hbm : b ≤ maximalIdeal R := le_maximalIdeal Ideal.IsPrime.ne_top'
  have ham : a < maximalIdeal R := hab.trans_le hbm
  by_cases hxP : x ∈ P
  · obtain ⟨i, hi⟩ := H a ‹_› hPa
    obtain ⟨Q₀, hQ₀, hQ₀a⟩ := Ideal.exists_minimalPrimes_le (sup_le hPa.le hi)
    exact hx Q₀ ⟨(hQ₀a.trans_lt ham).ne, i, hQ₀⟩ (le_sup_left.trans hQ₀.1.2 hxP)
  · obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le
      (show P ⊔ Ideal.span {x} ≤ maximalIdeal R from
        sup_le (le_maximalIdeal Ideal.IsPrime.ne_top') ((Ideal.span_singleton_le_iff_mem _).2 hxm))
    have := hQ.isPrime
    have hxQ : x ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
    have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2) fun h => hxP (h ▸ hxQ)
    have hQm : Q ≠ maximalIdeal R := by
      intro h
      rw [h] at hQ
      exact not_chain_of_mem_minimalPrimes hPa ham hQ
    obtain ⟨i, hi⟩ := H Q ‹_› hPQ
    obtain ⟨Q', hQ', hQ'Q⟩ := Ideal.exists_minimalPrimes_le (sup_le hPQ.le hi)
    have := hQ'.isPrime
    have hPQ' : P < Q' := lt_of_le_of_ne (le_sup_left.trans hQ'.1.2) fun h =>
      hI i (by rw [h]; exact le_sup_right.trans hQ'.1.2)
    obtain rfl : Q' = Q := by
      by_contra hne
      exact not_chain_of_mem_minimalPrimes hPQ' (lt_of_le_of_ne hQ'Q hne) hQ
    exact hx Q' ⟨hQm, i, hQ'⟩ hxQ

/-- Descent: from a prime `P` containing no `Iᵢ`, of finite coheight, one reaches a prime
`Q ≥ P` of coheight `≤ 1` containing no `Iᵢ`. -/
theorem exists_coheight_le_one (I : ℕ → Ideal R) (n : ℕ) :
    ∀ P : PrimeSpectrum R, Order.coheight P ≤ n → (∀ i, ¬ I i ≤ P.asIdeal) →
      ∃ Q : PrimeSpectrum R, P ≤ Q ∧ Order.coheight Q ≤ 1 ∧ ∀ i, ¬ I i ≤ Q.asIdeal := by
  induction n with
  | zero => exact fun P hP hI => ⟨P, le_rfl, hP.trans (by simp), hI⟩
  | succ n ih =>
    intro P hP hI
    by_cases h1 : Order.coheight P ≤ 1
    · exact ⟨P, le_rfl, h1, hI⟩
    push Not at h1
    have hfin : Order.coheight P < ⊤ := hP.trans_lt (ENat.natCast_lt_top _)
    obtain ⟨a, hPa, ha⟩ := (Order.coe_lt_coheight_iff (n := 1) hfin).1 (by simpa using h1)
    obtain ⟨b, hab⟩ := not_isMax_iff.1
      (Order.coheight_pos.1 (by rw [ha]; norm_num))
    obtain ⟨Q, hQ, hPQ, hQI⟩ := exists_isPrime_gt I hI (a := a.asIdeal) (b := b.asIdeal) hPa hab
    let Q' : PrimeSpectrum R := ⟨Q, hQ⟩
    have hlt : P < Q' := hPQ
    have hQ' : Order.coheight Q' ≤ n := by
      have := (Order.coheight_add_one_le hlt).trans hP
      rw [Nat.cast_succ] at this
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 this
    obtain ⟨T, hQT, hT1, hTI⟩ := ih Q' hQ' hQI
    exact ⟨T, hlt.le.trans hQT, hT1, hTI⟩

omit [IsAdicComplete (maximalIdeal R) R] in
lemma coheight_lt_top (x : PrimeSpectrum R) : Order.coheight x < ⊤ := by
  exact WithBot.coe_lt_coe.1 (((Order.coheight_le_krullDim x).trans_lt ringKrullDim_lt_top).trans_le (by simp))

/-- **Proposition of page 36**, in the form corrected by the edition. In the spectrum of a
complete noetherian local ring, countably many closed subsets whose union contains every point
`x` with `dim closure {x} ≤ 1` — the coheight of `x` in `Spec R` — have a finite subfamily
covering the spectrum. -/
theorem exists_finite_subcover (Z : ℕ → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hcov : ∀ x : PrimeSpectrum R, Order.coheight x ≤ 1 → x ∈ ⋃ i, Z i) :
    ∃ s : Finset ℕ, ⋃ i ∈ s, Z i = Set.univ := by
  let I : ℕ → Ideal R := fun i => vanishingIdeal (Z i)
  have hZI : ∀ i x, x ∈ Z i ↔ I i ≤ x.asIdeal := by
    intro i x
    rw [← SetLike.coe_subset_coe, ← mem_zeroLocus, zeroLocus_vanishingIdeal_eq_closure,
      (hZ i).closure_eq]
  by_contra! hfin
  obtain ⟨P, hP, hPI⟩ : ∃ P ∈ minimalPrimes R, ∀ i, ¬ I i ≤ P := by
    by_contra! h
    choose! g hg using h
    have hmin := Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥
    apply hfin (hmin.toFinset.image g)
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ x.asIdeal)
    exact Set.mem_biUnion (Finset.mem_image.2 ⟨P, hmin.mem_toFinset.2 hP, rfl⟩)
      ((hZI _ _).2 ((hg P hP).trans hPx))
  let P' : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (coheight_lt_top P').ne
  obtain ⟨Q, -, hQ1, hQI⟩ := exists_coheight_le_one I n P' hn.symm.le hPI
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov Q hQ1)
  exact hQI i ((hZI i Q).1 hi)

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
/-- In `Spec R`, `R` local, the closed point is the only point of coheight `0`. -/
lemma coheight_eq_zero_iff (x : PrimeSpectrum R) :
    Order.coheight x = 0 ↔ x = closedPoint R := by
  rw [Order.coheight_eq_zero]
  refine ⟨fun h => le_antisymm (le_maximalIdeal x.2.ne_top) (h (le_maximalIdeal x.2.ne_top)),
    ?_⟩
  rintro rfl y hy
  exact le_maximalIdeal y.2.ne_top

/-- The Proposition of page 36 for any countable index set. -/
theorem exists_finite_subcover_of_countable {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hcov : ∀ x : PrimeSpectrum R, Order.coheight x ≤ 1 → x ∈ ⋃ i, Z i) :
    ∃ s : Finset ι, ⋃ i ∈ s, Z i = Set.univ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := hcov (closedPoint R) (by rw [(coheight_eq_zero_iff _).2 rfl]; exact zero_le)
    simp at this
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  obtain ⟨s, hs⟩ := exists_finite_subcover (Z ∘ e) (fun _ => hZ _) fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov x hx)
    obtain ⟨n, rfl⟩ := he i
    exact Set.mem_iUnion.2 ⟨n, hi⟩
  classical
  refine ⟨s.image e, Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.1 (hs ▸ Set.mem_univ x)
  exact Set.mem_iUnion₂.2 ⟨e n, Finset.mem_image_of_mem e hn, hx⟩

/-- **Corollary of page 38.** Let `R` be a complete noetherian local domain which is not a
field. Countably many proper closed subsets of `Spec R` (in the irreducible space `Spec R`,
the closed subsets with empty interior, the page's « fermés rares », are exactly the proper
ones) miss some point `x` with `dim closure {x} = 1`. -/
theorem exists_coheight_eq_one [IsDomain R] (hR : ¬ IsField R) {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i)) (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, Order.coheight x = 1 ∧ ∀ i, x ∉ Z i := by
  let Z' : Option ι → Set (PrimeSpectrum R) := fun o => o.elim {closedPoint R} Z
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ o, η ∉ Z' o := by
    rintro (_ | i) h
    · have : (⊥ : Ideal R) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal h
      exact hR (IsLocalRing.isField_iff_maximalIdeal_eq.2 this.symm)
    · refine hZu i (Set.eq_univ_of_forall fun y => ?_)
      exact ((le_iff_specializes η y).1 bot_le).mem_closed (hZ i) h
  by_contra! H
  obtain ⟨s, hs⟩ := exists_finite_subcover_of_countable Z'
    (by rintro (_ | i); exacts [isClosed_singleton_closedPoint R, hZ i]) fun x hx => by
      by_cases h0 : Order.coheight x = 0
      · exact Set.mem_iUnion.2 ⟨none, (coheight_eq_zero_iff x).1 h0⟩
      · obtain ⟨i, hi⟩ := H x (le_antisymm hx (Order.one_le_iff_ne_zero.2 h0))
        exact Set.mem_iUnion.2 ⟨some i, hi⟩
  obtain ⟨o, -, ho⟩ := Set.mem_iUnion₂.1 (hs ▸ Set.mem_univ η)
  exact hη o ho

end Grothendieck.Folder100.Baire

/-!
## `dim closure {x}` as a topological dimension

The Corollary above measures `dim closure {x}` by the coheight of `x` in `Spec R`. Here that
choice is justified: for any commutative ring, the topological Krull dimension of the closure of
`x` (chains of irreducible closed subsets of the subspace `closure {x}`) is the coheight of `x`.
The closure is `V(x)` (`PrimeSpectrum.closure_singleton`), homeomorphic to `Spec (R ⧸ x)`
through the closed embedding `comap (R → R ⧸ x)`; its dimension is `dim R ⧸ x`
(`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`), which is the Krull dimension of the
poset `V(x) = Ici x` (`ringKrullDim_quotient`), i.e. the coheight of `x`.
-/

namespace Grothendieck.Folder100.Baire

open IsLocalRing PrimeSpectrum Topology

/-- For a point `x` of `Spec A`, the topological Krull dimension of `closure {x}` equals the
coheight of `x` (both are `dim A ⧸ x`). -/
theorem topologicalKrullDim_closure_singleton {A : Type*} [CommRing A] (x : PrimeSpectrum A) :
    topologicalKrullDim (closure ({x} : Set (PrimeSpectrum A))) = Order.coheight x := by
  have hs := Ideal.Quotient.mk_surjective (I := x.asIdeal)
  let e : PrimeSpectrum (A ⧸ x.asIdeal) ≃ₜ closure ({x} : Set (PrimeSpectrum A)) :=
    (isClosedEmbedding_comap_of_surjective _ _ hs).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (by rw [range_comap_of_surjective _ _ hs, Ideal.mk_ker, PrimeSpectrum.closure_singleton]))
  rw [← IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph,
    topologicalKrullDim_eq_ringKrullDim, ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- **Corollary of page 38, with `dim closure {x}` the topological dimension.** In `Spec R`,
`R` a complete noetherian local domain not a field, countably many proper closed subsets miss
some point `x` whose closure has topological Krull dimension `1`. -/
theorem exists_topologicalKrullDim_closure_eq_one [IsDomain R] (hR : ¬ IsField R)
    {ι : Type*} [Countable ι] (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hZu : ∀ i, Z i ≠ Set.univ) :
    ∃ x : PrimeSpectrum R, topologicalKrullDim (closure ({x} : Set (PrimeSpectrum R))) = 1 ∧
      ∀ i, x ∉ Z i := by
  obtain ⟨x, hx, hZx⟩ := exists_coheight_eq_one hR Z hZ hZu
  exact ⟨x, by rw [topologicalKrullDim_closure_singleton, hx]; rfl, hZx⟩

end Grothendieck.Folder100.Baire
