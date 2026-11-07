module

public import Mathlib
public import Grothendieck.Upstream.ChoosePrimePowSubOne

@[expose] public section


/-!
# Folder 136, pages 19–31: the binomial lemma behind the « ombres »

The modernised reading `transcripts/136/136.modern.tex` (« Coefficients binomiaux
modulo `p` », pages 19 to 22, and « Le théorème sur `M ⊗_k S` », pages 26 to 34)
states, with `c_{a,b} = binom(a + b, a)`:

> **Théorème 1 (p. 22).** Let `E` be an abelian group, `N ∈ ℕ`, and `(xᵢ)` in `E`
> with `binom(j, i) (x_j − x_i) = 0` for `j > i ≥ N`. Then `xᵢ = x_N` for every
> `i ≥ N`.
>
> **Théorème (pp. 26–31).** Let `0 ≤ i ≤ N`, `M` an abelian group and `(ξ_k)_{k ≥ N}`
> in `M` with `c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l}` for `k ≥ N`, `l ≥ 0`. There is a
> unique `ξ ∈ M` with `ξ_k = binom(k, i) ξ` for every `k ≥ N`.

Théorème 1 is the arithmetic core of finding `136-shadow-full-faithfulness` of
`src/content/findings.ts` (it gives Corollary 1: `ω_N : M ↦ M ⊗_k S^{+(N)}` is fully
faithful, a morphism being a family `u_k : M → M'` with `c_{k,j}(u_{k+j} − u_k) = 0`,
that is Théorème 1 in the group `M →+ M'`). The second theorem is the degree-`i`
form, `M T^{(i)} ≃ Hom^i(τ_{N−i} S, M ⊗_k S)`, written on coefficients. Proving them
says only that the claims hold as stated; whether they stand in the literature is a
separate question.

What is formalised.

* The second theorem, for every `i` (the hypothesis `i ≤ N` is not used)
  (`binomial_shadow_existsUnique`). The proof is not the page's: no localisation and
  no `p`-adic digit shift. With `K = p^r − 1` above `k` and `k'`, every `binom(K, ·)`
  is prime to `p` (`not_dvd_choose_pow_sub_one`, the « aucune retenue » of p. 31),
  and the relations from `k` and `k'` up to `K`, with the identity
  `binom(k+l, l) binom(k, i) = binom(k+l, i) binom(k+l−i, l)` (`choose_add_mul_choose`),
  give that `binom(k, i) ξ_{k'} − binom(k', i) ξ_k` is killed by an integer prime to
  `p`; for every `p` this forces it to vanish (`eq_zero_of_forall_prime_smul`, through
  the additive order). The `binom(k, i)`, `k ≥ N`, generate the unit ideal of `ℤ`
  (`span_choose_eq_top`), and a Bézout combination `∑ mₐ binom(kₐ, i) = 1` defines
  `ξ = ∑ mₐ ξ_{kₐ}` and gives its uniqueness, as on page 27.
* Théorème 1 (`binomial_constant`) is the case `i = 0`; the family of additive maps
  of Corollary 1 is its instance in `M →+ M'` (`hom_family_constant`).

Not formalised: the full faithfulness of `ω_N` and the isomorphism
`M ⊗_k S → φ_N τ_N (M ⊗_k S)` over the divided-power algebra `k{T}` as statements
about graded modules; Lemma 2 of page 21 (the `ℤ_(p)`-local form with few indices).
-/

namespace Grothendieck.Folder136

/-- No carry is possible: `p` divides no `binom(p^r − 1, b)`, `b ≤ p^r − 1`
(p. 31, « `μ + ν = p^r − 1` entraîne `c_{μ,ν} ≢ 0` »). In `ZMod p` the value is
`(-1)^b`. -/
theorem choose_pow_sub_one_zmod {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ∀ b, b ≤ p ^ r - 1 → ((p ^ r - 1).choose b : ZMod p) = (-1) ^ b := by
  have := Fact.mk hp
  have hpos : 0 < p ^ r := pow_pos hp.pos r
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    intro hb
    have hpascal : (p ^ r).choose (b + 1) =
        (p ^ r - 1).choose b + (p ^ r - 1).choose (b + 1) := by
      rw [← Nat.choose_succ_succ', Nat.sub_add_cancel (by omega : 1 ≤ p ^ r)]
    have h0 : ((p ^ r).choose (b + 1) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_choose_pow (by omega) (by omega))
    rw [hpascal, Nat.cast_add, ih (by omega)] at h0
    rw [pow_succ]
    linear_combination h0

theorem not_dvd_choose_pow_sub_one {p : ℕ} (hp : p.Prime) (r b : ℕ)
    (hb : b ≤ p ^ r - 1) : ¬ p ∣ (p ^ r - 1).choose b :=
  have := Fact.mk hp; Choose.not_dvd_choose_pow_sub_one hb

/-- `binom(k+l, l) binom(k, i) = binom(k+l, i) binom(k+l−i, l)` for all `k, l, i`. -/
theorem choose_add_mul_choose (k l i : ℕ) :
    (k + l).choose l * k.choose i = (k + l).choose i * (k + l - i).choose l := by
  rcases le_or_gt i k with hik | hik
  · have h := Nat.choose_mul (n := k + l) hik
    rwa [Nat.choose_symm_add, Nat.choose_symm_of_eq_add (show k + l - i = (k - i) + l by omega)]
      at h
  · rw [Nat.choose_eq_zero_of_lt hik, mul_zero]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [Nat.choose_eq_zero_of_lt hik]
    · rw [Nat.choose_eq_zero_of_lt (show k + l - i < l by omega), mul_zero]

/-- An element killed, for every prime `p`, by an integer prime to `p` is zero. -/
theorem eq_zero_of_forall_prime_smul {A : Type*} [AddCommGroup A] (z : A)
    (h : ∀ p : ℕ, p.Prime → ∃ c : ℕ, ¬ p ∣ c ∧ c • z = 0) : z = 0 := by
  by_contra hz
  have h1 : addOrderOf z ≠ 1 := by rwa [Ne, AddMonoid.addOrderOf_eq_one_iff]
  obtain ⟨c, hc, hcz⟩ := h _ (Nat.minFac_prime h1)
  exact hc ((Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hcz))

/-- For every prime `p` some `K = p^r − 1 ≥ m` exists. -/
theorem exists_pow_sub_one_ge {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∃ r, m ≤ p ^ r - 1 :=
  ⟨m, Nat.le_sub_one_of_lt (Nat.lt_pow_self hp.one_lt)⟩

/-- The cross relation `binom(k, i) ξ_{k'} = binom(k', i) ξ_k` for `k, k' ≥ N`. -/
theorem cross_relation {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l))
    {k k' : ℕ} (hk : N ≤ k) (hk' : N ≤ k') :
    k.choose i • ξ k' = k'.choose i • ξ k := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_prime_smul _ fun p hp => ?_
  obtain ⟨r, hr⟩ := exists_pow_sub_one_ge hp (k + k')
  set K := p ^ r - 1 with hK
  have e : k + (K - k) = K := by omega
  have e' : k' + (K - k') = K := by omega
  have h1 := h k (K - k) hk
  have h2 := h k' (K - k') hk'
  have i1 := choose_add_mul_choose k (K - k) i
  have i2 := choose_add_mul_choose k' (K - k') i
  rw [e] at h1 i1
  rw [e'] at h2 i2
  set u := K.choose (K - k)
  set u' := K.choose (K - k')
  set a := (K - i).choose (K - k)
  set a' := (K - i).choose (K - k')
  refine ⟨u * u', fun hd => ?_, ?_⟩
  · exact ((Nat.Prime.dvd_mul hp).1 hd).elim (not_dvd_choose_pow_sub_one hp r _ (by omega))
      (not_dvd_choose_pow_sub_one hp r _ (by omega))
  · rw [smul_sub, smul_smul, smul_smul,
      show u * u' * k.choose i = (u * k.choose i) * u' by ring,
      show u * u' * k'.choose i = (u' * k'.choose i) * u by ring,
      mul_smul, mul_smul (u' * _), h1, h2, i1, i2, smul_smul, smul_smul,
      show K.choose i * a * a' = K.choose i * a' * a by ring, sub_self]

/-- The binomial coefficients `binom(N + n, i)`, `n ∈ ℕ`, generate the unit ideal
of `ℤ`: for each `p`, `binom(p^r − 1, i)` with `p^r − 1 ≥ N + i` is prime to `p`. -/
theorem span_choose_eq_top (N i : ℕ) :
    Ideal.span (Set.range fun n : ℕ => ((N + n).choose i : ℤ)) = ⊤ := by
  set I := Ideal.span (Set.range fun n : ℕ => ((N + n).choose i : ℤ))
  obtain ⟨g, hg⟩ := (inferInstance : Submodule.IsPrincipal I)
  by_cases h1 : g.natAbs = 1
  · rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    exact Int.isUnit_iff_natAbs_eq.2 h1
  · exfalso
    set p := Nat.minFac g.natAbs with hpdef
    have hp : p.Prime := Nat.minFac_prime h1
    obtain ⟨r, hr⟩ := exists_pow_sub_one_ge hp (N + i)
    have hmem : ((N + (p ^ r - 1 - N)).choose i : ℤ) ∈ I := Ideal.subset_span ⟨_, rfl⟩
    rw [hg, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hmem
    have := Int.natCast_dvd_natCast.1 ((Int.natCast_dvd.2 (Nat.minFac_dvd _)).trans hmem)
    rw [show N + (p ^ r - 1 - N) = p ^ r - 1 by omega] at this
    exact not_dvd_choose_pow_sub_one hp r i (by omega) this

/-- **The theorem of pages 26–31**, for every `i`: if
`c_{l,k} ξ_k = c_{l,k−i} ξ_{k+l}` for `k ≥ N`, `l ≥ 0`, with `c_{a,b} = binom(a+b, a)`,
there is a unique `ξ` with `ξ_k = binom(k, i) ξ` for every `k ≥ N`. -/
theorem binomial_shadow_existsUnique {A : Type*} [AddCommGroup A] (ξ : ℕ → A) (N i : ℕ)
    (h : ∀ k l, N ≤ k → (k + l).choose l • ξ k = (k + l - i).choose l • ξ (k + l)) :
    ∃! x : A, ∀ k, N ≤ k → ξ k = k.choose i • x := by
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ (Set.range fun n : ℕ => ((N + n).choose i : ℤ)) :=
    Submodule.eq_top_iff'.1 (span_choose_eq_top N i) 1
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  simp only [smul_eq_mul] at hc
  -- `ξ = ∑ mₐ ξ_{N+a}` and, for any `y`, `y = ∑ mₐ binom(N+a, i) y`
  have hone : ∀ y : A, (c.sum fun n m => (m * ((N + n).choose i : ℤ)) • y) = y := fun y => by
    unfold Finsupp.sum at hc ⊢
    rw [← Finset.sum_smul, hc, one_smul]
  refine ⟨c.sum fun n m => m • ξ (N + n), ?_, ?_⟩
  · intro k hk
    rw [← natCast_zsmul, Finsupp.smul_sum]
    conv_lhs => rw [← hone (ξ k)]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [mul_smul, natCast_zsmul,
      ← cross_relation ξ N i h hk (show N ≤ N + n by omega), ← natCast_zsmul]
    exact smul_comm _ _ _
  · intro y hy
    rw [← hone y]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only
    rw [mul_smul, natCast_zsmul, ← hy (N + n) (by omega)]

/-- **Théorème 1 (p. 22).** If `binom(j, i)(x_j − x_i) = 0` for all `j > i ≥ N` in an
abelian group, then `x_j = x_N` for every `j ≥ N`. -/
theorem binomial_constant {A : Type*} [AddCommGroup A] (x : ℕ → A) (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (x j - x i) = 0) :
    ∀ j, N ≤ j → x j = x N := by
  have h' : ∀ k l, N ≤ k → (k + l).choose l • x k = (k + l - 0).choose l • x (k + l) := by
    intro k l hk
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have := h k (k + l) hk (by omega)
      rw [Nat.choose_symm_add, smul_sub, sub_eq_zero] at this
      rw [Nat.sub_zero, this]
  obtain ⟨y, hy, -⟩ := binomial_shadow_existsUnique x N 0 h'
  intro j hj
  rw [hy j hj, hy N le_rfl, Nat.choose_zero_right, Nat.choose_zero_right]

/-- Corollary 1 a) on coefficients: a family of additive maps `u_k : M → M'` with
`binom(j, k)(u_j − u_k) = 0` for `j > k ≥ N` is constant from `N` on. -/
theorem hom_family_constant {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (u : ℕ → M →+ M') (N : ℕ)
    (h : ∀ i j, N ≤ i → i < j → j.choose i • (u j - u i) = 0) :
    ∀ j, N ≤ j → u j = u N :=
  binomial_constant u N h

end Grothendieck.Folder136

/-!
# Folder 136, pages 5 to 10 and 226 to 232: the row of total degree `n` on one simplex

The reading (« La construction (pages 5 à 8) », « Les ombres (pages 9 à 11) », « Calculs
d'homotopie (pages 226 à 232) ») states, for `C^{p,q}_* = Γ^p Φ_* ⊗ Λ^q Ψ_*`, the simplicial
`k{T}`-algebra of divided-power forms on the simplex `∑ X_i = T`:

> For every simplicial set `X`, `H^{p,q}_DRpd(X, k) ≅ H^q(X, k)` for every `p ≥ 0`, and `0`
> for `p < 0`; graded by total degree, `H^{•,q} ≅ τ_{≥q}(H^q(X, k) ⊗_k k{T})`.

This is finding `136-pd-de-rham-shadows`. Its argument has two steps: each row of fixed total
degree `n`, `0 → k_* → C^{n,0}_* → ⋯ → C^{0,n}_* → 0`, is exact (page 8 says so without
proof; the reading supplies the divided-power Koszul complex), and its terms with `p ≥ 1` are
acyclic (Proposition 1 of page 226, `Φ_* ≃ 0`), so the row is a truncated acyclic resolution
of `k_*`.

What is formalised: the first step, and with it the statement for `X = Δ[m]`. On the
`m`-simplex the page itself identifies `C^{••}_{[m]}` with `k{T}{Y_1, …, Y_m}[dY_1, …, dY_m]`
(`Y_i = X_i`, `X_0 = T − ∑ Y_i`, `dT = 0`). A form is given by its coefficient function
`f a β I`, the coefficient of `T^{(a)} Y^{(β)} dY_I`, over any finite linearly ordered set of
variables `σ` (`σ = Fin m` for the `m`-simplex) and any commutative ring `k`.

* `pdD_pdD`: the differential squares to zero.
* `pdH_pdD_add`: an explicit contracting homotopy, `H d + d H = 1 − P`, `P` the projection on
  the constants `T^{(a)}`. It is the tensor-product homotopy of the one-variable complexes
  `Y^{(a)} ↦ Y^{(a−1)} dY`, taken at the least variable a monomial involves; it needs no
  division, which is the point of the divided powers (the Euler homotopy divides by the
  weight).
* `exact_of_pos`, `cocycle_zero`, `smul_tPow_eq_zero`: in total degree `n`, every cocycle of
  exterior degree `q ≥ 1` is a coboundary, and the cocycles of exterior degree `0` are the
  `c T^{(n)}`: the row is exact, with `H^{n,0} ≅ k` through the augmentation `1 ↦ T^{(n)}`.
* `pdD_tMul`, `tMul_tMul`, `tMul_tPow`: the `k{T}`-module structure, `d` is `k{T}`-linear and
  `T^{(j)} T^{(n)} = c_{j,n} T^{(n+j)}`; so, graded by total degree, the cohomology of one
  simplex is `k{T} = τ_{≥0}(k ⊗_k k{T})`, the shadow of `H^•(Δ[m], k) = k`.
* `pd_row_cohomology` gathers these.

Not formalised: the identification of `Γ^p Φ ⊗ Λ^q Ψ` with the coordinate model (Γ of a free
module, change of basis `X ↦ (T, Y)`) and its simplicial structure; Proposition 1
(`Φ_* ≃ 0`) and the acyclicity of `C^{p,q}_*` for `p ≥ 1`; the cohomology of a simplicial set
with coefficients in a simplicial module, hence the passage from `Δ[m]` to an arbitrary `X`.
-/

namespace Grothendieck.Folder136

open Finset

section PDKoszul

variable {k : Type*} [CommRing k] {σ : Type*} [LinearOrder σ]

/-- `(β − e_j) + e_j = β` when `β_j ≥ 1`. -/
theorem sub_single_add_single {β : σ → ℕ} {j : σ} (hβ : β j ≠ 0) :
    β - Pi.single j 1 + Pi.single j 1 = β := by
  ext x
  by_cases hx : x = j <;> simp [hx]; omega

/-- `(β + e_j) − e_j = β`. -/
theorem add_single_sub_single (β : σ → ℕ) (j : σ) :
    β + Pi.single j 1 - Pi.single j 1 = β := by
  ext x
  by_cases hx : x = j <;> simp [hx]

/-- `(β + e_i) − e_j = (β − e_j) + e_i` for `i ≠ j`. -/
theorem add_sub_comm_single (β : σ → ℕ) {i j : σ} (hij : i ≠ j) :
    β + Pi.single i 1 - Pi.single j 1 = β - Pi.single j 1 + Pi.single i 1 := by
  ext x
  by_cases hx : x = j <;> by_cases hx' : x = i <;> simp [*, Ne.symm hij]

/-- Removing `j > i` from `J` does not change the number of its elements below `i`. -/
theorem card_filter_lt_erase_of_lt {J : Finset σ} {i j : σ} (hij : i < j) :
    ((J.erase j).filter (· < i)).card = (J.filter (· < i)).card := by
  rw [filter_erase, erase_eq_of_notMem]
  simp [not_lt.2 hij.le]

/-- Removing `i ∈ J`, `i < j`, lowers the number of elements of `J` below `j` by one. -/
theorem card_filter_lt_erase_of_gt {J : Finset σ} {i j : σ} (hij : i < j) (hi : i ∈ J) :
    ((J.erase i).filter (· < j)).card + 1 = (J.filter (· < j)).card := by
  rw [filter_erase, card_erase_of_mem (by simp [hi, hij])]
  have : 0 < (J.filter (· < j)).card := card_pos.2 ⟨i, by simp [hi, hij]⟩
  omega

/-- The Koszul sign `(−1)^{#{i ∈ J | i < j}}` of `dY_j ∧ dY_{J ∖ j} = ± dY_J`. -/
def kSign (J : Finset σ) (j : σ) : k := (-1) ^ (J.filter (· < j)).card

/-- The two orders of removing `i` and `j` from `dY_J` differ by a sign. -/
theorem kSign_swap {J : Finset σ} {i j : σ} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j) :
    (kSign J j * kSign (J.erase j) i : k) = -(kSign J i * kSign (J.erase i) j) := by
  unfold kSign
  rcases lt_or_gt_of_ne hij with h | h
  · rw [card_filter_lt_erase_of_lt h, ← card_filter_lt_erase_of_gt h hi]
    ring
  · rw [card_filter_lt_erase_of_lt h, ← card_filter_lt_erase_of_gt h hj]
    ring

/-- The differential, on coefficient functions: `f(a, β, I)` is the coefficient of
`T^{(a)} Y^{(β)} dY_I`, and `d(Y^{(β)} dY_I) = ∑_j Y^{(β − e_j)} dY_j ∧ dY_I` gives
`(d f)(a, β, J) = ∑_{j ∈ J} ε(J, j) f(a, β + e_j, J ∖ j)`; `dT = 0`. -/
def pdD (f : ℕ → (σ → ℕ) → Finset σ → k) : ℕ → (σ → ℕ) → Finset σ → k :=
  fun a β J => ∑ j ∈ J, kSign J j * f a (β + Pi.single j 1) (J.erase j)

/-- `d ∘ d = 0`. -/
theorem pdD_pdD (f : ℕ → (σ → ℕ) → Finset σ → k) : pdD (pdD f) = 0 := by
  funext a β J
  simp only [pdD, Finset.mul_sum, Pi.zero_apply]
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ hx
    simp only [mem_sigma, mem_erase] at hx
    obtain ⟨hj, hij, hi⟩ := hx
    dsimp only
    rw [← mul_assoc, ← mul_assoc, kSign_swap hi hj hij, add_right_comm β, erase_right_comm]
    ring
  · rintro ⟨j, i⟩ hx _ h
    simp only [mem_sigma, mem_erase, Sigma.mk.inj_iff] at hx h
    exact hx.2.1 h.1
  · rintro ⟨j, i⟩ hx
    simp only [mem_sigma, mem_erase] at hx ⊢
    exact ⟨hx.2.2, Ne.symm hx.2.1, hx.1⟩
  · rintro ⟨j, i⟩ _
    rfl

variable [Fintype σ]

/-- The variables a monomial `Y^{(β)} dY_I` involves. -/
def pdSupp (β : σ → ℕ) (I : Finset σ) : Finset σ :=
  I ∪ univ.filter (fun i => β i ≠ 0)

/-- The contracting homotopy, through the least variable `j` a monomial involves: if `j ∈ I`,
`H(Y^{(β)} dY_I) = Y^{(β + e_j)} dY_{I ∖ j}`, otherwise `0`. On coefficients,
`(H f)(a, β, I) = f(a, β − e_j, I ∪ j)` when `j ∉ I`. Over `ℤ` the Euler homotopy would
divide by the weight; the divided powers make this one integral. -/
def pdH (f : ℕ → (σ → ℕ) → Finset σ → k) : ℕ → (σ → ℕ) → Finset σ → k :=
  fun a β I =>
    if h : (pdSupp β I).Nonempty then
      if (pdSupp β I).min' h ∈ I then 0
      else f a (β - Pi.single ((pdSupp β I).min' h) 1) (insert ((pdSupp β I).min' h) I)
    else 0

/-- The projection on the constants `T^{(a)}`. -/
def pdP (f : ℕ → (σ → ℕ) → Finset σ → k) : ℕ → (σ → ℕ) → Finset σ → k :=
  fun a β I => if pdSupp β I = ∅ then f a β I else 0

/-- `H` computed through any description of the leading variable `j`. -/
theorem pdH_of_least {f : ℕ → (σ → ℕ) → Finset σ → k} {a : ℕ} {β : σ → ℕ} {I : Finset σ}
    {j : σ} (hj : j ∈ pdSupp β I) (hmin : ∀ x ∈ pdSupp β I, j ≤ x) :
    pdH f a β I = if j ∈ I then 0 else f a (β - Pi.single j 1) (insert j I) := by
  have h : (pdSupp β I).Nonempty := ⟨j, hj⟩
  have e : (pdSupp β I).min' h = j := le_antisymm (min'_le _ _ hj) (le_min' _ _ _ hmin)
  simp [pdH, h, e]

/-- `H` vanishes on the constants. -/
theorem pdH_of_empty {f : ℕ → (σ → ℕ) → Finset σ → k} {a : ℕ} {β : σ → ℕ} {I : Finset σ}
    (h : pdSupp β I = ∅) : pdH f a β I = 0 := by
  simp [pdH, h]

/-- Moving `dY_i` into `Y^{(β)}` keeps the variables involved. -/
theorem pdSupp_add_erase {β : σ → ℕ} {I : Finset σ} {i : σ} (hi : i ∈ I) :
    pdSupp (β + Pi.single i 1) (I.erase i) = pdSupp β I := by
  ext x
  by_cases hx : x = i <;> simp [pdSupp, hx, hi, Pi.single_apply]

/-- Moving `Y_j` into `dY_I` keeps the variables involved. -/
theorem pdSupp_sub_insert {β : σ → ℕ} {I : Finset σ} {j : σ} (hβ : β j ≠ 0) :
    pdSupp (β - Pi.single j 1) (insert j I) = pdSupp β I := by
  ext x
  by_cases hx : x = j <;> simp [pdSupp, hx, hβ, Pi.single_apply]

/-- **The homotopy formula**: `H d + d H = 1 − P`, `P` the projection on the constants. -/
theorem pdH_pdD_add (f : ℕ → (σ → ℕ) → Finset σ → k) (a : ℕ) (β : σ → ℕ) (I : Finset σ) :
    pdH (pdD f) a β I + pdD (pdH f) a β I = f a β I - pdP f a β I := by
  by_cases hS : pdSupp β I = ∅
  · have hI : I = ∅ := by
      rw [← subset_empty, ← hS]; exact subset_union_left
    subst hI
    simp [pdH_of_empty hS, pdD, pdP, hS]
  have hne : (pdSupp β I).Nonempty := nonempty_iff_ne_empty.2 hS
  set j := (pdSupp β I).min' hne with hjdef
  have hjS : j ∈ pdSupp β I := min'_mem _ _
  have hmin : ∀ x ∈ pdSupp β I, j ≤ x := fun x hx => min'_le _ _ hx
  have hP : pdP f a β I = 0 := by simp [pdP, hS]
  rw [hP, sub_zero, pdH_of_least hjS hmin]
  -- `pdH f` on the faces `(β + e_i, I ∖ i)`, `i ∈ I`
  have hface : ∀ i ∈ I, pdH f a (β + Pi.single i 1) (I.erase i)
      = if j ∈ I.erase i then 0 else f a (β + Pi.single i 1 - Pi.single j 1) (insert j (I.erase i)) := by
    intro i hi
    rw [← pdSupp_add_erase (β := β) hi] at hjS hmin
    exact pdH_of_least hjS hmin
  by_cases hjI : j ∈ I
  · -- case B: the leading variable is a `dY_j`
    rw [ite_eq_left hjI, zero_add]
    simp only [pdD]
    rw [Finset.sum_eq_single j]
    · rw [hface j hjI, ite_eq_right (by simp), add_single_sub_single, insert_erase hjI]
      have : I.filter (· < j) = ∅ := by
        rw [filter_eq_empty_iff]
        intro x hx; exact not_lt.2 (hmin x (mem_union_left _ hx))
      simp [kSign, this]
    · intro i hi hij
      rw [hface i hi, ite_eq_left (mem_erase.2 ⟨Ne.symm hij, hjI⟩), mul_zero]
    · intro h; exact absurd hjI h
  · -- case A: the leading variable is a `Y_j`
    rw [ite_eq_right hjI]
    have hβ : β j ≠ 0 := by
      have := hjS; simp only [pdSupp, mem_union, mem_filter, mem_univ, true_and] at this
      tauto
    have hlt : ∀ i ∈ I, j < i := fun i hi =>
      lt_of_le_of_ne (hmin i (mem_union_left _ hi)) (fun h => hjI (h ▸ hi))
    simp only [pdD]
    rw [sum_insert hjI, sub_single_add_single hβ, erase_insert hjI]
    have h0 : kSign (insert j I) j = (1 : k) := by
      have : (insert j I).filter (· < j) = ∅ := by
        rw [filter_eq_empty_iff]
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact lt_irrefl _
        · exact not_lt.2 (hlt x hx).le
      simp [kSign, this]
    rw [h0, one_mul, add_assoc, add_eq_left, ← sum_add_distrib]
    refine sum_eq_zero fun i hi => ?_
    rw [hface i hi, ite_eq_right (fun h => hjI (mem_of_mem_erase h)),
      erase_insert_of_ne (hlt i hi).ne, add_sub_comm_single β (hlt i hi).ne']
    have hs : kSign (insert j I) i = -(kSign I i : k) := by
      unfold kSign
      rw [filter_insert, ite_eq_left (hlt i hi), card_insert_of_notMem (fun h => hjI (mem_filter.1 h).1)]
      ring
    rw [hs]; ring

/-- Bidegree `(n, q)`: total degree `a + |β| + |I| = n`, exterior degree `|I| = q`. -/
def IsBideg (n q : ℕ) (f : ℕ → (σ → ℕ) → Finset σ → k) : Prop :=
  ∀ a β I, f a β I ≠ 0 → a + ∑ i, β i + I.card = n ∧ I.card = q

/-- `|β + e_j| = |β| + 1`. -/
theorem sum_add_single (β : σ → ℕ) (j : σ) :
    ∑ i, (β + Pi.single j 1 : σ → ℕ) i = ∑ i, β i + 1 := by
  simp [sum_add_distrib, sum_pi_single']

/-- `d` has bidegree `(−1, +1)`: total degree kept, exterior degree raised. -/
theorem IsBideg.pdD {n q : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k} (hf : IsBideg n q f) :
    IsBideg n (q + 1) (pdD f) := by
  intro a β J h
  obtain ⟨j, hj, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  have := hf _ _ _ (right_ne_zero_of_mul hne)
  rw [sum_add_single, card_erase_of_mem hj] at this
  have : 0 < J.card := card_pos.2 ⟨j, hj⟩
  omega

/-- `H` has bidegree `(+1, −1)`. -/
theorem IsBideg.pdH {n q : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k} (hf : IsBideg n (q + 1) f) :
    IsBideg n q (pdH f) := by
  intro a β I h
  unfold Grothendieck.Folder136.pdH at h
  split_ifs at h with h1 h2
  · exact absurd rfl h
  swap
  · exact absurd rfl h
  set j := (pdSupp β I).min' h1
  have hβ : β j ≠ 0 := by
    have := min'_mem (pdSupp β I) h1
    simp only [pdSupp, mem_union, mem_filter, mem_univ, true_and] at this
    tauto
  have := hf _ _ _ h
  rw [card_insert_of_notMem h2] at this
  have e := sum_add_single (β - Pi.single j 1) j
  rw [sub_single_add_single hβ] at e
  omega

omit [LinearOrder σ] in
/-- Nothing in exterior degree `q > n` (« `p ≥ 0` », p. 8). -/
theorem IsBideg.eq_zero_of_gt {n q : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k} (hf : IsBideg n q f)
    (h : n < q) : f = 0 := by
  funext a β I
  by_contra hne
  have := hf a β I hne
  omega

/-- **Exactness of the row in exterior degree `q ≥ 1`**: a cocycle of bidegree `(n, q)` is the
coboundary of a form of bidegree `(n, q − 1)`, namely of `H f`. -/
theorem exact_of_pos {n q : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k} (hf : IsBideg n (q + 1) f)
    (hd : pdD f = 0) : IsBideg n q (pdH f) ∧ pdD (pdH f) = f := by
  refine ⟨hf.pdH, ?_⟩
  funext a β I
  have h := pdH_pdD_add f a β I
  have hP : pdP f a β I = 0 := by
    unfold pdP
    split_ifs with hS
    · have hI : I = ∅ := by rw [← subset_empty, ← hS]; exact subset_union_left
      by_contra hne
      have := (hf a β I hne).2
      rw [hI] at this
      simp at this
    · rfl
  rw [hd, hP, sub_zero] at h
  simpa [pdH] using h

/-- The class `T^{(n)}`: the coefficient function of `T^{(n)} Y^{(0)} dY_∅`. -/
def tPow (n : ℕ) : ℕ → (σ → ℕ) → Finset σ → k :=
  fun a β I => if a = n ∧ β = 0 ∧ I = ∅ then 1 else 0

/-- A monomial involves no variable iff it is a `T^{(a)}`. -/
theorem pdSupp_eq_empty {β : σ → ℕ} {I : Finset σ} : pdSupp β I = ∅ ↔ β = 0 ∧ I = ∅ := by
  constructor
  · intro h
    have hI : I = ∅ := by rw [← subset_empty, ← h]; exact subset_union_left
    refine ⟨funext fun i => ?_, hI⟩
    by_contra hi
    have : i ∈ pdSupp β I := mem_union_right _ (by simpa using hi)
    rw [h] at this; simp at this
  · rintro ⟨rfl, rfl⟩
    simp [pdSupp]

/-- `T^{(n)}` has bidegree `(n, 0)`. -/
theorem tPow_isBideg (n : ℕ) : IsBideg n 0 (tPow n : ℕ → (σ → ℕ) → Finset σ → k) := by
  intro a β I h
  unfold tPow at h
  split_ifs at h with h'
  swap
  · exact absurd rfl h
  obtain ⟨rfl, rfl, rfl⟩ := h'
  simp

/-- `d T^{(n)} = 0` (`dT = ∑ dX_i = 0`). -/
theorem pdD_tPow (n : ℕ) : pdD (tPow n : ℕ → (σ → ℕ) → Finset σ → k) = 0 := by
  funext a β J
  refine sum_eq_zero fun j _ => ?_
  have : β + Pi.single j 1 ≠ 0 := fun h => by simpa using congrFun h j
  simp [tPow, this]

/-- `H 0 = 0`. -/
theorem pdH_zero : pdH (0 : ℕ → (σ → ℕ) → Finset σ → k) = 0 := by
  funext a β I
  simp [pdH]

/-- `H` kills exterior degree `0`. -/
theorem pdH_eq_zero_of_isBideg_zero {n : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k}
    (hf : IsBideg n 0 f) : pdH f = 0 := by
  funext a β I
  by_contra h
  simp only [Pi.zero_apply] at h
  unfold Grothendieck.Folder136.pdH at h
  split_ifs at h with h1 h2
  · exact absurd rfl h
  swap
  · exact absurd rfl h
  have := (hf _ _ _ h).2
  simp at this

/-- **Exterior degree `0`**: the cocycles of bidegree `(n, 0)` are the `c T^{(n)}`, and
`c ↦ c T^{(n)}` is injective: `H^{n,0} ≅ k`, through the augmentation `1 ↦ T^{(n)}`. -/
theorem cocycle_zero {n : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k} (hf : IsBideg n 0 f)
    (hd : pdD f = 0) : f = f n 0 ∅ • tPow n := by
  funext a β I
  have h := pdH_pdD_add f a β I
  rw [hd, pdH_zero, pdH_eq_zero_of_isBideg_zero hf] at h
  simp only [Pi.zero_apply, pdD, mul_zero, sum_const_zero, add_zero] at h
  rw [eq_comm, sub_eq_zero] at h
  rw [h]
  simp only [pdP, pdSupp_eq_empty, Pi.smul_apply, tPow, smul_eq_mul]
  by_cases hβI : β = 0 ∧ I = ∅
  · obtain ⟨rfl, rfl⟩ := hβI
    by_cases ha : a = n
    · subst ha; simp
    · have : f a 0 ∅ = 0 := by
        by_contra hne
        have := (hf a 0 ∅ hne).1
        simp at this; exact ha this
      simp [this, ha]
  · simp only [hβI, ↓reduceIte]
    rw [ite_eq_right (by tauto), mul_zero]

/-- The augmentation `1 ↦ T^{(n)}` is injective. -/
theorem smul_tPow_eq_zero {n : ℕ} {c : k} (h : c • (tPow n : ℕ → (σ → ℕ) → Finset σ → k) = 0) :
    c = 0 := by
  simpa [tPow] using congrFun (congrFun (congrFun h n) 0) ∅

/-- Multiplication by `T^{(j)}`: `T^{(j)} T^{(a)} = c_{j,a} T^{(a+j)}`, so the coefficient of
`T^{(a)}` in `T^{(j)} f` is `binom(a, j)` times that of `T^{(a−j)}` in `f`. -/
def tMul (j : ℕ) (f : ℕ → (σ → ℕ) → Finset σ → k) : ℕ → (σ → ℕ) → Finset σ → k :=
  fun a β I => if j ≤ a then (a.choose j : k) * f (a - j) β I else 0

omit [Fintype σ] in
/-- The differential is `k{T}`-linear. -/
theorem pdD_tMul (j : ℕ) (f : ℕ → (σ → ℕ) → Finset σ → k) :
    pdD (tMul j f) = tMul j (pdD f) := by
  funext a β J
  simp only [pdD, tMul]
  split_ifs
  · rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; ring
  · simp

omit [LinearOrder σ] [Fintype σ] in
/-- `T^{(i)} (T^{(j)} f) = c_{i,j} T^{(i+j)} f`: the forms are a `k{T}`-module. -/
theorem tMul_tMul (i j : ℕ) (f : ℕ → (σ → ℕ) → Finset σ → k) :
    tMul i (tMul j f) = ((i + j).choose i : k) • tMul (i + j) f := by
  funext a β I
  simp only [tMul, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i + j ≤ a
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hij,
      show a - i - j = a - (i + j) by omega, ← mul_assoc, ← mul_assoc]
    congr 1
    have := Nat.choose_mul (n := a) (k := i + j) (s := i) (by omega)
    rw [Nat.add_sub_cancel_left] at this
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact congrArg _ (this.symm.trans (mul_comm _ _))
  · rw [ite_eq_right hij, mul_zero]
    split_ifs with h1 h2
    · omega
    · rw [mul_zero]
    · rfl

omit [LinearOrder σ] in
/-- `T^{(j)}` sends total degree `n` to `n + j`. -/
theorem IsBideg.tMul {n q : ℕ} {f : ℕ → (σ → ℕ) → Finset σ → k} (hf : IsBideg n q f) (j : ℕ) :
    IsBideg (n + j) q (tMul j f) := by
  intro a β I h
  unfold Grothendieck.Folder136.tMul at h
  split_ifs at h with hj
  · have := hf _ _ _ (right_ne_zero_of_mul h)
    omega
  · exact absurd rfl h

/-- **The shadow structure** (p. 9): `T^{(j)} T^{(n)} = c_{j,n} T^{(n+j)}`. -/
theorem tMul_tPow (j n : ℕ) :
    tMul j (tPow n : ℕ → (σ → ℕ) → Finset σ → k) = ((n + j).choose j : k) • tPow (n + j) := by
  funext a β I
  simp only [tMul, tPow, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j ≤ a
  · rw [ite_eq_left hj]
    by_cases ha : a = n + j
    · subst ha; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero, mul_zero]
  · rw [ite_eq_right hj, ite_eq_right (by omega), mul_zero]

/-- **The row of total degree `n` (pp. 8–9, 232), on one simplex.** In the model of
`C^{••}_{[m]} ≅ k{T} ⊗ Ω_pd(k{Y_1, …, Y_m})` (`σ = Fin m`), in total degree `n`:
every cocycle of exterior degree `q + 1` is a coboundary; the cocycles of exterior degree
`0` are the `c T^{(n)}`, `c ∈ k` unique, so `H^{n−q,q} = 0` for `q ≥ 1` and
`H^{n,0} ≅ k` through `1 ↦ T^{(n)}`; nothing lives in exterior degree `q > n`; and
`T^{(j)}` sends the class `T^{(n)}` to `c_{j,n} T^{(n+j)}`. Graded by total degree,
the cohomology is `k{T} = τ_{≥0}(H^0 ⊗_k k{T})`, the shadow of `H^•(Δ[m], k) = k`. -/
theorem pd_row_cohomology (n : ℕ) :
    (∀ q (f : ℕ → (σ → ℕ) → Finset σ → k), IsBideg n (q + 1) f → pdD f = 0 →
        ∃ g, IsBideg n q g ∧ pdD g = f) ∧
    (∀ f : ℕ → (σ → ℕ) → Finset σ → k, IsBideg n 0 f → pdD f = 0 →
        ∃! c : k, f = c • tPow n) ∧
    (IsBideg n 0 (tPow n : ℕ → (σ → ℕ) → Finset σ → k) ∧ pdD (tPow n : ℕ → (σ → ℕ) → Finset σ → k) = 0) ∧
    (∀ q (f : ℕ → (σ → ℕ) → Finset σ → k), n < q → IsBideg n q f → f = 0) ∧
    (∀ j, tMul j (tPow n : ℕ → (σ → ℕ) → Finset σ → k) = ((n + j).choose j : k) • tPow (n + j)) := by
  refine ⟨fun q f hf hd => ⟨_, exact_of_pos hf hd⟩, fun f hf hd => ⟨_, cocycle_zero hf hd, ?_⟩,
    ⟨tPow_isBideg n, pdD_tPow n⟩, fun q f h hf => hf.eq_zero_of_gt h, fun j => tMul_tPow j n⟩
  intro c hc
  refine eq_of_sub_eq_zero (smul_tPow_eq_zero (n := n) (σ := σ) ?_)
  rw [sub_smul, ← hc, ← cocycle_zero hf hd, sub_self]

end PDKoszul

end Grothendieck.Folder136

/-!
# Folder 136, pages 5 to 7: the coordinate model is `Γ^•Φ ⊗ Λ^qΨ`, simplicially

The section above works in the coordinate model `k{T}{Y_1, …, Y_m}[dY_1, …, dY_m]` that
pages 5–7 give for `C^{••}_{[m]}`. Here the model is identified with the reading's
`C^{•,q}_{[m]} = Γ_k(Φ_[m]) ⊗_k Λ^q_k Ψ_[m]`, `Φ_[m] = k^{m+1}`, `Ψ_[m] = Φ_[m]/k·T`,
`T = ∑ Xᵢ = (1, …, 1)`, over any commutative ring `k`, and the simplicial structure is built.

* `dp_prod_linearIndependent`, `dpBasis`: **the basis theorem for `Γ` of a free module of
  finite rank** — for a basis `(bᵢ)` of `M`, the `∏ᵢ bᵢ^{(aᵢ)}` are a basis of `Γ_k(M)`.
  Mathlib defines `Γ_k(M)` (`DividedPowerAlgebra`) and proves that these products span; their
  independence is new here. The proof maps `Γ_k(M)` to the convolution algebra
  `(Sym M^∨)^*` of the primitively generated bialgebra `Sym M^∨`, by `x^{(n)} ↦ (coefficient of
  Xⁿ in φ ↦ φ(x) X)` (`pdRep`, the four relations `pdF_zero`, `pdF_smul`, `pdF_mul`,
  `pdF_add`); there `∏ᵢ bᵢ^{(aᵢ)}` becomes the coefficient of `X^a` after
  `φ ↦ ∑ φ(bᵢ) Xᵢ` (`pdRep_prod`), which is `1` on `∏ (b^∨ᵢ)^{aᵢ}` and `0` on the other
  monomials. No division is used.
* `tyBasis`: the basis `T, Y₁, …, Y_m` (`Yᵢ = Xᵢ`, `X₀ = T − ∑ Yᵢ`) of `Φ_[m]`;
  `psiBasis`: the basis `dY₁, …, dY_m` of `Ψ_[m]`; `pdModelBasis`, `pdModelBasis_apply`: the
  basis `T^{(a)} Y^{(β)} ⊗ dY_I`, `|I| = q`, of `Γ(Φ_[m]) ⊗ Λ^qΨ_[m]` — exactly the
  monomials whose coefficients `f a β I` the section above works with.
* `dp_one_mul_dpBasis`: `T^{(j)} T^{(a)} Y^{(β)} = c_{j,a} T^{(a+j)} Y^{(β)}`, the
  `k{T}`-module structure `tMul` of the coefficient model.
* `pdSimplicial`: the simplicial `k`-module `[n] ↦ Γ(Φ_[n]) ⊗ Λ^qΨ_[n]`, `θ ↦ Γ(Φ(θ)) ⊗
  Λ^q(Ψ(θ))`, `Φ(θ) = (f ↦ f ∘ θ)` (`pdModelMap_id`, `pdModelMap_comp`); `pdModelMap_tPow`:
  `T^{(p)}` is a simplicial section, the augmentation `k_* → C^{p,0}_*`.

Not formalised: the differential `d(x^{(n)}) = x^{(n−1)} dx` on `Γ(Φ) ⊗ Λ^•Ψ` and its
agreement with `pdD` in the basis, the grading by `p` (Mathlib's `Γ` is not yet graded) and
the product of `Γ ⊗ Λ^•`, the presentation `S{X₀, …, X_n}[dX]/(∑Xᵢ − t, ∑dXᵢ)_pd` of page 5,
and the transport of the face maps into the coordinates `(T, Y)`.
-/

open TensorProduct Coalgebra WithConv Polynomial Finset

namespace Grothendieck.Folder136

section PDBasis

variable (k : Type*) [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]

local notation "Cd" => SymmetricAlgebra k (Module.Dual k M)

/-- Evaluation at `m`: `Sym M^∨ → k[X]`, `φ ↦ φ(m) X`. -/
noncomputable def pdEv (m : M) : Cd →ₐ[k] k[X] :=
  SymmetricAlgebra.lift ((Module.Dual.eval k M m).smulRight X)

@[simp] theorem pdEv_ι (m : M) (φ : Module.Dual k M) :
    pdEv k m (SymmetricAlgebra.ι k _ φ) = φ m • X := by
  simp [pdEv]

/-- The image of `m^{(n)}`: the coefficient of `Xⁿ` after `pdEv m`. -/
noncomputable def pdF (p : ℕ × M) : WithConv (Cd →ₗ[k] k) :=
  toConv (lcoeff k p.1 ∘ₗ (pdEv k p.2).toLinearMap)

theorem pdF_zero (m : M) : pdF k (0, m) = 1 := by
  have : (Polynomial.aeval (0 : k)).comp (pdEv k m) = Bialgebra.counitAlgHom k Cd :=
    SymmetricAlgebra.algHom_ext (by ext; simp [SymmetricAlgebra.algebraMapInv_ι])
  apply ofConv_injective; ext c
  rw [pdF, ofConv_toConv, LinearMap.comp_apply, lcoeff_apply, coeff_zero_eq_eval_zero,
    ← coe_aeval_eq_eval]
  exact congr($this c)

theorem coeff_aeval_C_mul_X (r : k) (n : ℕ) (q : k[X]) :
    (aeval (C r * X) q).coeff n = r ^ n * q.coeff n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial N a =>
    simp only [aeval_monomial, algebraMap_eq, mul_pow, ← C_pow, ← mul_assoc, ← C_mul,
      coeff_C_mul_X_pow, coeff_monomial]
    split_ifs <;> simp_all [mul_comm]

theorem pdF_smul (n : ℕ) (r : k) (m : M) : pdF k (n, r • m) = r ^ n • pdF k (n, m) := by
  have : pdEv k (r • m) = (aeval (C r * X)).comp (pdEv k m) :=
    SymmetricAlgebra.algHom_ext (by ext; simp [smul_eq_C_mul, mul_assoc, coeff_C_mul, mul_left_comm])
  apply ofConv_injective; ext c
  simp [pdF, this, coeff_aeval_C_mul_X]

/-- `(a ⊗ 1 + 1 ⊗ b)^N = ∑ binom(N, i) aⁱ ⊗ bʲ`. -/
theorem add_tmul_one_pow {A B : Type*} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    (a : A) (b : B) (N : ℕ) : (a ⊗ₜ[k] (1 : B) + 1 ⊗ₜ b) ^ N =
      ∑ x ∈ antidiagonal N, N.choose x.1 • ((a ^ x.1) ⊗ₜ[k] (b ^ x.2)) := by
  rw [(Commute.all _ _).add_pow']
  simp [Algebra.TensorProduct.tmul_pow]

/-- The comultiplication of `k[X]`, `X ↦ X ⊗ 1 + 1 ⊗ X`. -/
noncomputable abbrev polyComul : k[X] →ₐ[k] k[X] ⊗[k] k[X] := aeval (X ⊗ₜ 1 + 1 ⊗ₜ X)

theorem pdEv_comul (m : M) :
    (Algebra.TensorProduct.map (pdEv k m) (pdEv k m)).comp (Bialgebra.comulAlgHom k Cd) =
      (polyComul k).comp (pdEv k m) :=
  SymmetricAlgebra.algHom_ext (by ext; simp [smul_tmul'])

theorem polyComul_monomial (N : ℕ) (a : k) :
    polyComul k (monomial N a) =
      ∑ x ∈ antidiagonal N, (a * N.choose x.1) • (((X : k[X]) ^ x.1) ⊗ₜ[k] ((X : k[X]) ^ x.2)) := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, add_tmul_one_pow, aeval_C, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_smul, ← Algebra.smul_def, Nat.cast_smul_eq_nsmul]

theorem polyComul_coeff (n p : ℕ) (q : k[X]) :
    LinearMap.mul' k k (map (lcoeff k n) (lcoeff k p) (polyComul k q)) =
      (n + p).choose n * q.coeff (n + p) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial N a =>
    rw [polyComul_monomial, map_sum, map_sum]
    by_cases h : n + p = N
    · subst h
      rw [sum_eq_single (n, p) (fun x hx hne => ?_) (by simp)]
      · simp [mul_comm]
      · rw [HasAntidiagonal.mem_antidiagonal] at hx
        simp only [map_smul, map_tmul, lcoeff_apply, coeff_X_pow, LinearMap.mul'_apply]
        split_ifs <;> simp_all [Prod.ext_iff]
    · rw [sum_eq_zero fun x hx => ?_]
      · simp [coeff_monomial, Ne.symm h]
      rw [HasAntidiagonal.mem_antidiagonal] at hx
      simp only [map_smul, map_tmul, lcoeff_apply, coeff_X_pow, LinearMap.mul'_apply]
      split_ifs <;> simp_all

theorem pdF_map_comul (n p : ℕ) (u v : M) (c : Cd) :
    map (pdF k (n, u)).ofConv (pdF k (p, v)).ofConv (comul c) =
      map (lcoeff k n) (lcoeff k p)
        (Algebra.TensorProduct.map (pdEv k u) (pdEv k v) (Bialgebra.comulAlgHom k Cd c)) := by
  rw [pdF, pdF, ofConv_toConv, ofConv_toConv, TensorProduct.map_comp]
  rfl

theorem pdF_mul (n p : ℕ) (m : M) :
    pdF k (n, m) * pdF k (p, m) = (n + p).choose n • pdF k (n + p, m) := by
  apply ofConv_injective; ext c
  rw [LinearMap.convMul_apply, pdF_map_comul, ← AlgHom.comp_apply, pdEv_comul, AlgHom.comp_apply,
    polyComul_coeff, ofConv_smul]
  simp [pdF]

theorem coeff_lmul' (n : ℕ) (t : k[X] ⊗[k] k[X]) :
    ∑ x ∈ antidiagonal n, LinearMap.mul' k k (map (lcoeff k x.1) (lcoeff k x.2) t) =
      (Algebra.TensorProduct.lmul' k t).coeff n := by
  induction t with
  | tmul x y => simp [coeff_mul]
  | add x y hx hy => simp [sum_add_distrib, hx, hy]

theorem pdF_add (n : ℕ) (u v : M) :
    pdF k (n, u + v) = ∑ x ∈ antidiagonal n, pdF k (x.1, u) * pdF k (x.2, v) := by
  have : ((Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map (pdEv k u)
      (pdEv k v))).comp (Bialgebra.comulAlgHom k Cd) = pdEv k (u + v) :=
    SymmetricAlgebra.algHom_ext (by ext; simp [add_smul])
  apply ofConv_injective; ext c
  simp only [ofConv_sum, LinearMap.sum_apply, LinearMap.convMul_apply, pdF_map_comul]
  rw [coeff_lmul', ← AlgHom.comp_apply, ← AlgHom.comp_apply, this]
  rfl

/-- The algebra map `Γ(M) → (Sym M^∨)^*`, `x^{(n)} ↦ (φ₁ ⋯ φ_r ↦ [r = n] ∏ φᵢ(x))`. -/
noncomputable def pdRep : DividedPowerAlgebra k M →ₐ[k] WithConv (Cd →ₗ[k] k) :=
  DividedPowerAlgebra.lift' (f := pdF k) (pdF_zero k) (pdF_smul k) (pdF_mul k) (pdF_add k)

theorem pdRep_dp (n : ℕ) (m : M) : pdRep k (DividedPowerAlgebra.dp k n m) = pdF k (n, m) :=
  DividedPowerAlgebra.lift'_apply_dp ..

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (b : Module.Basis σ k M)

/-- `Sym M^∨ → k[X_σ]`, `φ ↦ ∑ φ(bᵢ) Xᵢ`. -/
noncomputable def pdCoordEv : Cd →ₐ[k] MvPolynomial σ k :=
  SymmetricAlgebra.lift (∑ i, (Module.Dual.eval k M (b i)).smulRight (MvPolynomial.X i))

omit [DecidableEq σ] in
@[simp] theorem pdCoordEv_ι (φ : Module.Dual k M) :
    pdCoordEv k b (SymmetricAlgebra.ι k _ φ) = ∑ i, φ (b i) • MvPolynomial.X i := by
  simp [pdCoordEv]

/-- `Xⱼ ↦ 1 ⊗ Xⱼ` for `j ≠ i`, `Xᵢ ↦ X ⊗ 1 + 1 ⊗ Xᵢ`. -/
noncomputable def pdTheta (i : σ) : MvPolynomial σ k →ₐ[k] k[X] ⊗[k] MvPolynomial σ k :=
  MvPolynomial.aeval fun j => (if j = i then X else 0) ⊗ₜ 1 + 1 ⊗ₜ MvPolynomial.X j

theorem pdEv_comul_EV (i : σ) :
    (Algebra.TensorProduct.map (pdEv k (b i)) (pdCoordEv k b)).comp (Bialgebra.comulAlgHom k Cd) =
      (pdTheta k i).comp (pdCoordEv k b) :=
  SymmetricAlgebra.algHom_ext (by
    ext φ; simp [pdTheta, smul_add, sum_add_distrib, tmul_sum, smul_tmul', ite_tmul, smul_ite])

omit [Fintype σ] in
theorem pdTheta_monomial (i : σ) (γ : σ →₀ ℕ) (c : k) :
    pdTheta k i (MvPolynomial.monomial γ c) =
      ((X : k[X]) ⊗ₜ[k] (1 : MvPolynomial σ k) + 1 ⊗ₜ MvPolynomial.X i) ^ γ i *
        (1 ⊗ₜ MvPolynomial.monomial (γ.erase i) c) := by
  conv_lhs => rw [← Finsupp.single_add_erase i γ, ← one_mul c, ← MvPolynomial.monomial_mul_monomial,
    ← MvPolynomial.X_pow_eq_monomial]
  rw [map_mul, map_pow, pdTheta, MvPolynomial.aeval_X, MvPolynomial.monomial_eq,
    map_mul, MvPolynomial.aeval_C, map_finsuppProd]
  simp only [↓reduceIte]
  congr 1
  rw [← Algebra.TensorProduct.includeRight_apply, map_mul,
    map_finsuppProd, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  refine congrArg _ (Finsupp.prod_congr fun j hj => ?_)
  rw [Finsupp.support_erase, mem_erase] at hj
  simp [hj.1]

omit [Fintype σ] in
theorem pdTheta_coeff (i : σ) (n : ℕ) {a : σ →₀ ℕ} (ha : a i = 0) (q : MvPolynomial σ k) :
    LinearMap.mul' k k (TensorProduct.map (lcoeff k n) (MvPolynomial.lcoeff k a) (pdTheta k i q)) =
      q.coeff (Finsupp.single i n + a) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial γ c =>
    have key : ∀ x ∈ antidiagonal (γ i), LinearMap.mul' k k (TensorProduct.map (lcoeff k n)
        (MvPolynomial.lcoeff k a) ((γ i).choose x.1 • (((X : k[X]) ^ x.1) ⊗ₜ[k]
          (MvPolynomial.X i ^ x.2)) * (1 ⊗ₜ MvPolynomial.monomial (γ.erase i) c))) =
        if x = (n, 0) ∧ γ.erase i = a then c else 0 := by
      rintro ⟨x1, x2⟩ hx
      rw [HasAntidiagonal.mem_antidiagonal] at hx
      have e : Finsupp.single i x2 + γ.erase i = a ↔ x2 = 0 ∧ γ.erase i = a := by
        refine ⟨fun h => ?_, fun h => by simp [h.1, h.2]⟩
        have h2 : x2 = 0 := by simpa [ha] using DFunLike.congr_fun h i
        exact ⟨h2, by simpa [h2] using h⟩
      rw [smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul]
      simp only [map_nsmul, map_tmul, lcoeff_apply, coeff_X_pow, MvPolynomial.lcoeff_apply,
        MvPolynomial.coeff_monomial, LinearMap.mul'_apply, e]
      by_cases h1 : n = x1 <;> by_cases h2 : x2 = 0 <;> simp [h1, h2, @eq_comm _ x1] at hx ⊢
      subst hx; simp
    rw [pdTheta_monomial, add_tmul_one_pow, sum_mul, map_sum, map_sum, sum_congr rfl key]
    have e : γ = Finsupp.single i n + a ↔ γ i = n ∧ γ.erase i = a := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · subst h; simp [ha, Finsupp.erase_add]
      · rw [← Finsupp.single_add_erase i γ, h.1, h.2]
    simp only [ite_and, sum_ite_eq', MvPolynomial.coeff_monomial, e,
      HasAntidiagonal.mem_antidiagonal, add_zero, @eq_comm _ n]

/-- The coefficient of `X^a` after `pdCoordEv`: the dual basis element of `∏ bᵢ^{(aᵢ)}`. -/
noncomputable def pdFF (a : σ →₀ ℕ) : WithConv (Cd →ₗ[k] k) :=
  toConv (MvPolynomial.lcoeff k a ∘ₗ (pdCoordEv k b).toLinearMap)

omit [DecidableEq σ] in
theorem pdFF_zero : pdFF k b 0 = 1 := by
  have : (MvPolynomial.aeval (0 : σ → k)).comp (pdCoordEv k b) = Bialgebra.counitAlgHom k Cd :=
    SymmetricAlgebra.algHom_ext (by ext; simp [SymmetricAlgebra.algebraMapInv_ι])
  apply ofConv_injective; ext c
  have h := congr($this c)
  rw [AlgHom.comp_apply, MvPolynomial.aeval_zero, Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

theorem pdF_mul_pdFF (i : σ) (n : ℕ) {a : σ →₀ ℕ} (ha : a i = 0) :
    pdF k (n, b i) * pdFF k b a = pdFF k b (Finsupp.single i n + a) := by
  apply ofConv_injective; ext c
  have : TensorProduct.map (pdF k (n, b i)).ofConv (pdFF k b a).ofConv (comul c) =
      TensorProduct.map (lcoeff k n) (MvPolynomial.lcoeff k a)
        (Algebra.TensorProduct.map (pdEv k (b i)) (pdCoordEv k b) (Bialgebra.comulAlgHom k Cd c)) := by
    rw [pdF, pdFF, ofConv_toConv, ofConv_toConv, TensorProduct.map_comp]
    rfl
  rw [LinearMap.convMul_apply, this, ← AlgHom.comp_apply, pdEv_comul_EV, AlgHom.comp_apply,
    pdTheta_coeff k i n ha]
  rfl

theorem pdRep_prod (a : σ →₀ ℕ) :
    pdRep k (a.prod fun i n => DividedPowerAlgebra.dp k n (b i)) = pdFF k b a := by
  induction a using Finsupp.induction with
  | zero => simp [pdFF_zero]
  | single_add i n a hi hn ih =>
    rw [Finsupp.prod_add_index_of_disjoint (by simp [hn, hi]),
      Finsupp.prod_single_index (by exact DividedPowerAlgebra.dp_zero), map_mul, ih, pdRep_dp,
      pdF_mul_pdFF k b i n (Finsupp.notMem_support_iff.1 hi)]

/-- The monomial `∏ⱼ (b^∨ⱼ)^{γⱼ}` of `Sym M^∨`. -/
noncomputable def pdTest (γ : σ →₀ ℕ) : Cd := γ.prod fun j e => SymmetricAlgebra.ι k _ (b.coord j) ^ e

omit [DecidableEq σ] in
theorem pdCoordEv_test (γ : σ →₀ ℕ) : pdCoordEv k b (pdTest k b γ) = MvPolynomial.monomial γ 1 := by
  simp [pdTest, Finsupp.prod, MvPolynomial.prod_X_pow_eq_monomial]

/-- **The basis theorem for `Γ` of a free module of finite rank**: if `(bᵢ)` is a basis of
`M`, the products `∏ᵢ bᵢ^{(aᵢ)}`, `a ∈ ℕ^{(σ)}`, are a basis of `Γ_k(M)`, over any commutative
ring `k`. -/
theorem dp_prod_linearIndependent :
    LinearIndependent k (fun a : σ →₀ ℕ => a.prod fun i n => DividedPowerAlgebra.dp k n (b i)) := by
  refine LinearIndependent.of_comp (pdRep k).toLinearMap (linearIndependent_iff'.2 ?_)
  intro s g hg a ha
  simpa [pdRep_prod, pdFF, pdCoordEv_test, MvPolynomial.coeff_monomial, ha] using
    congr(($hg).ofConv (pdTest k b a))

/-- The basis `∏ᵢ bᵢ^{(aᵢ)}` of `Γ_k(M)`. -/
noncomputable def dpBasis : Module.Basis (σ →₀ ℕ) k (DividedPowerAlgebra k M) :=
  .mk (dp_prod_linearIndependent k b)
    (DividedPowerAlgebra.submodule_span_prod_dp_eq_top b.span_eq).ge

theorem dpBasis_apply (a : σ →₀ ℕ) :
    dpBasis k b a = a.prod fun i n => DividedPowerAlgebra.dp k n (b i) :=
  Module.Basis.mk_apply ..

end PDBasis

section PDModel

variable (k : Type*) [CommRing k] (m : ℕ)

/-- The coordinates `(T, Y₁, …, Y_m)` on `Φ_[m] = k^{m+1}`: `T = ∑ Xᵢ`, `Yᵢ = Xᵢ`, so
`X₀ = T − ∑ Yᵢ`. -/
def tyEquiv : (Fin (m + 1) → k) ≃ₗ[k] (Option (Fin m) → k) where
  toFun f o := o.elim (f 0) fun i => f i.succ - f 0
  invFun c := Fin.cases (c none) fun i => c (some i) + c none
  map_add' f g := by ext (_ | i) <;> simp; ring
  map_smul' r f := by ext (_ | i) <;> simp [mul_sub]
  left_inv f := by ext j; cases j using Fin.cases <;> simp
  right_inv c := by ext (_ | i) <;> simp

/-- The basis `T = (1, …, 1)`, `Yᵢ = e_{i+1}` of `Φ_[m]`. -/
noncomputable def tyBasis : Module.Basis (Option (Fin m)) k (Fin (m + 1) → k) :=
  .ofEquivFun (tyEquiv k m)

@[simp] theorem tyBasis_none : tyBasis k m none = 1 := by
  ext j; cases j using Fin.cases <;> simp [tyBasis, tyEquiv, Module.Basis.coe_ofEquivFun]

@[simp] theorem tyBasis_some (i : Fin m) : tyBasis k m (some i) = Pi.single i.succ 1 := by
  ext j; cases j using Fin.cases <;> simp [tyBasis, tyEquiv, Module.Basis.coe_ofEquivFun,
    Pi.single_apply]

/-- `Ψ_[m] = Φ_[m] / k·T`. -/
abbrev PsiM := (Fin (m + 1) → k) ⧸ (k ∙ (1 : Fin (m + 1) → k))

/-- `f ↦ (f(i+1) − f(0))ᵢ`, the coordinates `Yᵢ` modulo `T`. -/
def psiCoord : (Fin (m + 1) → k) →ₗ[k] (Fin m → k) where
  toFun f i := f i.succ - f 0
  map_add' f g := by ext; simp; ring
  map_smul' r f := by ext; simp [mul_sub]

theorem ker_psiCoord : LinearMap.ker (psiCoord k m) = k ∙ (1 : Fin (m + 1) → k) := by
  ext f
  simp only [LinearMap.mem_ker, Submodule.mem_span_singleton, funext_iff, psiCoord,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, sub_eq_zero]
  refine ⟨fun h => ⟨f 0, fun j => ?_⟩, fun ⟨a, h⟩ i => by simp [← h]⟩
  cases j using Fin.cases <;> simp [h]

theorem psiCoord_surjective : Function.Surjective (psiCoord k m) :=
  fun c => ⟨Fin.cases 0 c, by ext; simp [psiCoord]⟩

/-- `Ψ_[m] ≃ k^m`. -/
noncomputable def psiEquiv : PsiM k m ≃ₗ[k] (Fin m → k) :=
  (Submodule.quotEquivOfEq _ _ (ker_psiCoord k m).symm).trans
    ((psiCoord k m).quotKerEquivOfSurjective (psiCoord_surjective k m))

/-- The basis `dY₁, …, dY_m` of `Ψ_[m]`: the classes of the `Yᵢ`. -/
noncomputable def psiBasis : Module.Basis (Fin m) k (PsiM k m) :=
  (Pi.basisFun k (Fin m)).map (psiEquiv k m).symm

theorem psiBasis_apply (i : Fin m) :
    psiBasis k m i = Submodule.mkQ _ (Pi.single i.succ 1) := by
  rw [psiBasis, Module.Basis.map_apply, LinearEquiv.symm_apply_eq]
  ext j
  rw [psiEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp [psiCoord, Pi.single_apply]

/-- The term `Γ(Φ_[m]) ⊗ Λ^q Ψ_[m]` of the bigraded algebra, all `p` at once. -/
abbrev PDModel (q : ℕ) := DividedPowerAlgebra k (Fin (m + 1) → k) ⊗[k] ⋀[k]^q (PsiM k m)

variable {k m}

/-- `Ψ(θ)`: `Φ(θ) = (f ↦ f ∘ θ)` fixes `T`, so passes to `Ψ = Φ/k·T`. -/
noncomputable def psiMap {n : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) : PsiM k m →ₗ[k] PsiM k n :=
  Submodule.mapQ _ _ (LinearMap.funLeft k k θ)
    (Submodule.span_singleton_le_iff_mem _ _ |>.2 (Submodule.mem_span_singleton_self _))

/-- The simplicial operator `θ^* = Γ(Φ(θ)) ⊗ Λ^q(Ψ(θ))`. -/
noncomputable def pdModelMap (q : ℕ) {n : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) :
    PDModel k m q →ₗ[k] PDModel k n q :=
  TensorProduct.map (DividedPowerAlgebra.map k (LinearMap.funLeft k k θ)).toLinearMap
    (exteriorPower.map q (psiMap θ))

theorem pdModelMap_id (q : ℕ) : pdModelMap (k := k) (m := m) q id = LinearMap.id := by
  have h1 : LinearMap.funLeft k k (id : Fin (m + 1) → Fin (m + 1)) = LinearMap.id := rfl
  have h2 : psiMap (k := k) (id : Fin (m + 1) → Fin (m + 1)) = LinearMap.id := by
    rw [psiMap, ← Submodule.mapQ_id]; rfl
  rw [pdModelMap, h1, h2, DividedPowerAlgebra.map_id, exteriorPower.map_id]
  exact TensorProduct.map_id

theorem pdModelMap_comp (q : ℕ) {n l : ℕ} (θ : Fin (n + 1) → Fin (m + 1))
    (θ' : Fin (l + 1) → Fin (n + 1)) :
    pdModelMap (k := k) q (θ ∘ θ') = pdModelMap q θ' ∘ₗ pdModelMap q θ := by
  have h1 : LinearMap.funLeft k k (θ ∘ θ') =
      LinearMap.funLeft k k θ' ∘ₗ LinearMap.funLeft k k θ := rfl
  have h2 : psiMap (k := k) (θ ∘ θ') = psiMap θ' ∘ₗ psiMap θ := by
    rw [psiMap, psiMap, psiMap, ← Submodule.mapQ_comp]; rfl
  rw [pdModelMap, pdModelMap, pdModelMap, h1, h2, DividedPowerAlgebra.map_comp,
    exteriorPower.map_comp, ← TensorProduct.map_comp]
  rfl

variable (k) in
/-- **The simplicial `k`-module `C^{•,q}_* = Γ^•Φ_* ⊗ Λ^qΨ_*`** (pages 5–7), with
`Φ_* : [n] ↦ k^{n+1}` and `Ψ_* = Φ_*/k_*`. -/
noncomputable def pdSimplicial (q : ℕ) : CategoryTheory.Functor SimplexCategoryᵒᵖ (ModuleCat k) where
  obj n := ModuleCat.of k (PDModel k n.unop.len q)
  map θ := ModuleCat.ofHom (pdModelMap q θ.unop.toOrderHom)
  map_id _ := ModuleCat.hom_ext (pdModelMap_id q)
  map_comp θ θ' := ModuleCat.hom_ext (pdModelMap_comp q θ.unop.toOrderHom θ'.unop.toOrderHom)

/-- `T^{(p)}` is a simplicial section: `θ^*(T^{(p)} ⊗ ω) = T^{(p)} ⊗ θ^*ω`, so
`1 ↦ T^{(p)}` is the augmentation `k_* → C^{p,0}_*`. -/
theorem pdModelMap_tPow (q : ℕ) {n : ℕ} (θ : Fin (n + 1) → Fin (m + 1)) (p : ℕ)
    (w : ⋀[k]^q (PsiM k m)) :
    pdModelMap q θ (DividedPowerAlgebra.dp k p 1 ⊗ₜ w) =
      DividedPowerAlgebra.dp k p 1 ⊗ₜ exteriorPower.map q (psiMap θ) w := by
  simp [pdModelMap]
  rfl

end PDModel

section PDModelBasis

variable (k : Type*) [CommRing k] (m : ℕ)

/-- **The coordinate model** (pages 5–7): `C^{•,q}_{[m]} = Γ(Φ_[m]) ⊗ Λ^qΨ_[m]` is free on
the `T^{(a)} Y^{(β)} ⊗ dY_I`, `a ∈ ℕ`, `β ∈ ℕ^m`, `I ⊆ {1, …, m}` with `|I| = q`. -/
noncomputable def pdModelBasis (q : ℕ) :
    Module.Basis ((Option (Fin m) →₀ ℕ) × Set.powersetCard (Fin m) q) k (PDModel k m q) :=
  (dpBasis k (tyBasis k m)).tensorProduct ((psiBasis k m).exteriorPower q)

theorem pdModelBasis_apply (q : ℕ) (a : Option (Fin m) →₀ ℕ) (I : Set.powersetCard (Fin m) q) :
    pdModelBasis k m q (a, I) = (a.prod fun o n => DividedPowerAlgebra.dp k n (tyBasis k m o)) ⊗ₜ
      exteriorPower.ιMulti_family k q (psiBasis k m) I := by
  simp [pdModelBasis, dpBasis_apply]

/-- **The `k{T}`-module structure** in the basis: `T^{(j)} · T^{(a)} Y^{(β)} =
c_{j,a} T^{(a+j)} Y^{(β)}`, the multiplication `tMul` of the coefficient model. -/
theorem dp_one_mul_dpBasis (j : ℕ) (a : Option (Fin m) →₀ ℕ) :
    DividedPowerAlgebra.dp k j 1 * dpBasis k (tyBasis k m) a =
      (a none + j).choose j • dpBasis k (tyBasis k m) (a + Finsupp.single none j) := by
  have h (b : Option (Fin m) →₀ ℕ) := (Finsupp.mul_prod_erase' b none
    (fun o n => DividedPowerAlgebra.dp k n (tyBasis k m o))
    (fun _ => DividedPowerAlgebra.dp_zero)).symm
  rw [dpBasis_apply, dpBasis_apply, h a, h (a + _), ← mul_assoc, ← tyBasis_none k m,
    DividedPowerAlgebra.dp_mul, Finsupp.erase_add, Finsupp.erase_single, add_zero]
  simp [add_comm j, mul_assoc]

end PDModelBasis

end Grothendieck.Folder136
