module

public import Mathlib

@[expose] public section


/-!
# Folder 94, pages 8, 9 and 19: regular sequences over a non-reduced base

The modernised reading `transcripts/94/94.modern.tex` states on pages 8–9 (Lemme 6) and 19
(Lemme 16) a substitute for generic flatness over a non-reduced base: for `S = Spec A`
noetherian and `R` coherent, there is a dense open `U ⊆ S` such that
`Tor_i^A(R, A_𝔭/(t)) = 0` for `i > 0`, `𝔭 ∈ U` and every `A_𝔭`-regular sequence `t`. This is
finding `94-generic-tor-regular-sequences`.

The argument of the reading (Lemme 6 b), with the flatness variant of Lemme 16): let `J` be a
nilpotent ideal of `A` (the nilradical, localised at `𝔭`), `A₀ = A/J`, and suppose that the
layers `grᵏ_J(A) = JᵏA/Jᵏ⁺¹A` are free `A₀`-modules and the layers `grᵏ_J(R) = JᵏR/Jᵏ⁺¹R`
flat `A₀`-modules. Then every `A`-regular sequence is `R`-regular; since the Koszul complex
of an `A`-regular sequence `t` resolves `A/(t)`, its homology after `⊗ R` is
`Tor_•^A(R, A/(t))`, which vanishes in positive degrees once `t` is `R`-regular.

Proved here, for any commutative ring `A`, any nilpotent ideal `J` and any `A`-module `R`
(no noetherian or finiteness hypothesis on `R`, so that the case of Lemme 16, `R` coherent on
an `X` of finite type over `S`, is covered):

* `isWeaklyRegular_iff_of_exact`, `injective_mapQ_of_exact`: for a short exact sequence
  `0 → M' → M → M'' → 0` and a sequence `rs` weakly regular on `M''`, `rs` is weakly regular on
  `M'` iff on `M`, and `M'/(rs)M' → M/(rs)M` is injective (the `Tor₁` that the reading kills);
* `isWeaklyRegular_quotient_filt`, `isWeaklyRegular_of_layers`: dévissage along the `J`-adic
  filtration — a sequence weakly regular on every layer is weakly regular on `M`;
* `isWeaklyRegular_quotient_of_layers_free`: if the layers of a nonzero `M` are free over
  `A₀`, every `M`-weakly regular sequence has weakly regular image in `A₀` (the induction step
  of Lemme 6, « bien standard si n = 1, et on continue par récurrence »);
* `isWeaklyRegular_of_flat`: flat `A₀`-modules inherit weak regularity from `A₀`;
* `isWeaklyRegular_of_gr` (main theorem): layers of `A` free and layers of `R` flat over
  `A₀` ⟹ every `A`-weakly regular sequence is `R`-weakly regular;
* `isWeaklyRegular_of_gr_flat_of_isLocalRing`: the stalk form used on pages 9 and 19: over a
  noetherian local ring, flatness of the layers of `A` suffices (they are then free), and
  `isRegular_of_gr_flat_of_isLocalRing` gives a regular sequence for a nonzero finite `R` and
  `t` in the maximal ideal.

**What is not formalised.** The step « `t` is `R`-regular ⟹ `Tor_i^A(R, A/(t)) = 0` for
`i > 0` » (Koszul complex; Mathlib has neither Koszul resolutions nor the long exact sequence of
`Tor`) is cited, not proved; only its `Tor₁`-type consequence `injective_mapQ_of_exact` is.
The dense open `U` is not constructed: for `X = S` it is the free locus of the finitely many
nonzero layers over the reduced ring `A₀` (generic freeness, open and containing the minimal
primes), and for `X` of finite type it needs generic flatness, which Mathlib does not have;
the compatibility of the layers with localisation is not written out either.
-/

open RingTheory.Sequence Submodule Function

namespace Grothendieck.Folder94

variable {A : Type*} [CommRing A]

section Exact

variable {M M' M'' N N' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  [AddCommGroup M''] [Module A M''] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']

/-- Every sequence is weakly regular on the zero module. -/
theorem isWeaklyRegular_of_subsingleton [Subsingleton N] (rs : List A) : IsWeaklyRegular N rs := by
  induction rs generalizing N with
  | nil => exact IsWeaklyRegular.nil A N
  | cons x rs ih =>
    exact IsWeaklyRegular.cons (fun a b _ => Subsingleton.elim a b) ih

/-- A retract inherits weak regularity. -/
theorem isWeaklyRegular_of_retract {i : N →ₗ[A] N'} {p : N' →ₗ[A] N}
    (hpi : p ∘ₗ i = LinearMap.id) {rs : List A} (h : IsWeaklyRegular N' rs) :
    IsWeaklyRegular N rs := by
  induction rs generalizing N N' with
  | nil => exact IsWeaklyRegular.nil A N
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at h
    refine IsWeaklyRegular.cons (h.1.of_injective i (LeftInverse.injective (g := p)
      (LinearMap.congr_fun hpi))) (ih (i := QuotSMulTop.map x i)
      (p := QuotSMulTop.map x p) ?_ h.2)
    rw [← QuotSMulTop.map_comp, hpi, QuotSMulTop.map_id]

/-- Modding out by an element regular on the cokernel keeps a short exact sequence injective
on the left. -/
theorem injective_map_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) {x : A} (hx : IsSMulRegular M'' x) : Injective (QuotSMulTop.map x f) := by
  have := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    ((LinearMap.exact_zero_iff_injective (PUnit : Type) f).mpr hf) hfg hx
  rwa [map_zero, LinearMap.exact_zero_iff_injective] at this

/-- **Two out of three.** For a short exact sequence `0 → M' → M → M'' → 0` and `rs` weakly
regular on `M''`, `rs` is weakly regular on `M'` iff it is on `M`. -/
theorem isWeaklyRegular_iff_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) (hg : Surjective g) {rs : List A} (h'' : IsWeaklyRegular M'' rs) :
    IsWeaklyRegular M' rs ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M' M M'' with
  | nil => exact ⟨fun _ => IsWeaklyRegular.nil A M, fun _ => IsWeaklyRegular.nil A M'⟩
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at h''
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff,
      ih (injective_map_of_exact hf hfg h''.1) (QuotSMulTop.map_exact x hfg hg)
        (QuotSMulTop.map_surjective x hg) h''.2]
    refine and_congr_left' ⟨fun h => ?_, fun h => h.of_injective f hf⟩
    exact isSMulRegular_of_range_eq_ker hf (LinearMap.exact_iff.mp hfg).symm h h''.1

/-- For a short exact sequence `0 → M' → M → M'' → 0` and `rs` weakly regular on `M''`, the map
`M'/(rs)M' → M/(rs)M` is injective: the vanishing of `Tor₁(M'', A/(rs))` in this guise. -/
theorem injective_mapQ_of_exact {f : M' →ₗ[A] M} {g : M →ₗ[A] M''} (hf : Injective f)
    (hfg : Exact f g) (hg : Surjective g) {rs : List A} (h'' : IsWeaklyRegular M'' rs) :
    Injective (mapQ _ _ f (smul_top_le_comap_smul_top (Ideal.ofList rs) f)) := by
  have := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
    ((LinearMap.exact_zero_iff_injective (PUnit : Type) f).mpr hf) hfg hg h''
  rw [← LinearMap.exact_zero_iff_injective (PUnit : Type)]
  refine fun y => ⟨fun hy => ?_, fun ⟨z, hz⟩ => ?_⟩
  · obtain ⟨z, rfl⟩ := (this y).mp hy
    exact ⟨0, by simp⟩
  · rw [← hz]; simp

end Exact

section Filtration

variable (J : Ideal A) (M : Type*) [AddCommGroup M] [Module A M]

/-- The `J`-adic filtration `JᵏM`. -/
abbrev filt (k : ℕ) : Submodule A M := J ^ k • ⊤

/-- The layer `grᵏ_J(M) = JᵏM / Jᵏ⁺¹M`. -/
abbrev layer (k : ℕ) : Type _ := ↥(filt J M k) ⧸ (filt J M (k + 1)).comap (filt J M k).subtype

variable {J M}

theorem filt_antitone {j k : ℕ} (h : j ≤ k) : filt J M k ≤ filt J M j :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

theorem filt_zero : filt J M 0 = ⊤ := by simp [filt]

/-- The inclusion `grᵏ(M) → M/Jᵏ⁺¹M`. -/
def layerToQuot (k : ℕ) : layer J M k →ₗ[A] M ⧸ filt J M (k + 1) :=
  mapQ _ _ (filt J M k).subtype le_rfl

/-- The projection `M/Jᵏ⁺¹M → M/JᵏM`. -/
def quotToQuot (k : ℕ) : M ⧸ filt J M (k + 1) →ₗ[A] M ⧸ filt J M k :=
  factor (filt_antitone (Nat.le_succ k))

theorem layerToQuot_injective (k : ℕ) : Injective (layerToQuot (J := J) (M := M) k) := by
  rw [← LinearMap.ker_eq_bot, layerToQuot, ker_mapQ]
  exact mkQ_map_self _

theorem quotToQuot_surjective (k : ℕ) : Surjective (quotToQuot (J := J) (M := M) k) :=
  factor_surjective (filt_antitone (Nat.le_succ k))

theorem exact_layerToQuot (k : ℕ) :
    Exact (layerToQuot (J := J) (M := M) k) (quotToQuot k) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H m =>
    constructor
    · intro hm
      exact ⟨Submodule.Quotient.mk ⟨m, by simpa [quotToQuot] using hm⟩, rfl⟩
    · rintro ⟨z, hz⟩
      rw [← hz]
      induction z using Submodule.Quotient.induction_on with
      | H z => simp [quotToQuot, layerToQuot]

/-- **Dévissage.** If `rs` is weakly regular on the layers `grᵏ(M)` for `k < j`, it is weakly
regular on `M/JʲM`. -/
theorem isWeaklyRegular_quotient_filt {rs : List A} :
    ∀ j, (∀ k < j, IsWeaklyRegular (layer J M k) rs) →
      IsWeaklyRegular (M ⧸ filt J M j) rs
  | 0, _ => by
    have : Subsingleton (M ⧸ filt J M 0) := by rw [filt_zero]; infer_instance
    exact isWeaklyRegular_of_subsingleton rs
  | j + 1, h =>
    (isWeaklyRegular_iff_of_exact (layerToQuot_injective j) (exact_layerToQuot j)
      (quotToQuot_surjective j) (isWeaklyRegular_quotient_filt j fun k hk => h k (by omega))).mp
      (h j (by omega))

/-- If `JⁿM = 0` and `rs` is weakly regular on every layer, it is weakly regular on `M`. -/
theorem isWeaklyRegular_of_layers {n : ℕ} (hn : filt J M n = ⊥) {rs : List A}
    (h : ∀ k, IsWeaklyRegular (layer J M k) rs) : IsWeaklyRegular M rs := by
  have := isWeaklyRegular_quotient_filt n fun k _ => h k
  rw [hn] at this
  exact ((quotEquivOfEqBot (⊥ : Submodule A M) rfl).isWeaklyRegular_congr rs).mp this

end Filtration

section Main

variable {J : Ideal A}

/-- A flat `A/J`-module inherits weak regularity from `A/J`. -/
theorem isWeaklyRegular_of_flat (N : Type*) [AddCommGroup N] [Module (A ⧸ J) N] [Module A N]
    [IsScalarTower A (A ⧸ J) N] [Module.Flat (A ⧸ J) N] {rs : List A}
    (h : IsWeaklyRegular (A ⧸ J) rs) : IsWeaklyRegular N rs := by
  rw [← isWeaklyRegular_map_algebraMap_iff (A ⧸ J) N]
  rw [← isWeaklyRegular_map_algebraMap_iff (A ⧸ J) (A ⧸ J)] at h
  exact ((TensorProduct.rid (A ⧸ J) N).isWeaklyRegular_congr _).mp
    (h.isWeaklyRegular_lTensor (M₂ := N))

/-- **The induction step of Lemme 6.** If `JⁿM = 0`, `M ≠ 0` and every layer `grᵏ_J(M)` is a free
`A/J`-module, every sequence weakly regular on `M` has weakly regular image in `A/J`. The last
nonzero layer `JᵐM` is a submodule of `M`, free and nonzero over `A/J`; modulo `(t₁, …, tᵢ)` it
still injects into `M/(t₁, …, tᵢ)M`, because `M/JᵐM` is filtered by free layers on which the
`tⱼ` are already known to be regular. -/
theorem isWeaklyRegular_quotient_of_layers_free {M : Type*} [AddCommGroup M] [Module A M]
    [Nontrivial M] {n : ℕ} (hn : filt J M n = ⊥) (ι : ℕ → Type*)
    (e : ∀ k, layer J M k ≃ₗ[A] (ι k →₀ A ⧸ J)) {rs : List A} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular (A ⧸ J) rs := by
  classical
  have hex : ∃ k, filt J M (k + 1) = ⊥ :=
    ⟨n, eq_bot_iff.mpr ((filt_antitone (Nat.le_succ n)).trans hn.le)⟩
  set m := Nat.find hex with hmdef
  have hm : filt J M (m + 1) = ⊥ := Nat.find_spec hex
  have hm0 : filt J M m ≠ ⊥ := by
    intro h0
    rcases m.eq_zero_or_pos with hz | hs
    · rw [hz, filt_zero] at h0
      exact top_ne_bot h0
    · have := Nat.find_min' hex (m := m - 1) (by rwa [Nat.sub_add_cancel hs])
      omega
  have hcomap : (filt J M (m + 1)).comap (filt J M m).subtype = ⊥ := by
    rw [hm, comap_bot, ker_subtype]
  let eL : ↥(filt J M m) ≃ₗ[A] (ι m →₀ A ⧸ J) :=
    (quotEquivOfEqBot _ hcomap).symm.trans (e m)
  have hne : Nonempty (ι m) := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Subsingleton ↥(filt J M m) := eL.toEquiv.subsingleton
    exact hm0 Submodule.eq_bot_of_subsingleton
  obtain ⟨i⟩ := hne
  induction rs using List.reverseRecOn with
  | nil => exact IsWeaklyRegular.nil _ _
  | append_singleton rs y ih =>
    rw [isWeaklyRegular_append_iff] at h
    have h0 := ih h.1
    have hlay : ∀ k, IsWeaklyRegular (layer J M k) rs := fun k =>
      ((e k).isWeaklyRegular_congr rs).mpr (isWeaklyRegular_of_flat _ h0)
    have hq : IsWeaklyRegular (M ⧸ filt J M m) rs :=
      isWeaklyRegular_quotient_filt m fun k _ => hlay k
    have hf := Submodule.injective_subtype (filt J M m)
    have hfg := LinearMap.exact_subtype_mkQ (filt J M m)
    have hg := (filt J M m).mkQ_surjective
    have hinj := injective_mapQ_of_exact hf hfg hg hq
    refine isWeaklyRegular_of_retract (i := Finsupp.lsingle (R := A) i)
      (p := Finsupp.lapply (R := A) i) (by ext; simp) ((eL.isWeaklyRegular_congr _).mp ?_)
    rw [isWeaklyRegular_append_iff]
    refine ⟨(isWeaklyRegular_iff_of_exact hf hfg hg hq).mpr h.1, ?_⟩
    have h2 := h.2
    rw [isWeaklyRegular_singleton_iff] at h2 ⊢
    exact h2.of_injective _ hinj

/-- **Lemmes 6 b) and 16, key step.** Let `J` be a nilpotent ideal of `A` (`Jⁿ = 0`), `A₀ = A/J`.
If every layer `grᵏ_J(A)` is a free `A₀`-module and every layer `grᵏ_J(R)` is a flat
`A₀`-module, every `A`-weakly regular sequence is `R`-weakly regular. -/
theorem isWeaklyRegular_of_gr {R : Type*} [AddCommGroup R] [Module A R] {n : ℕ} (hn : J ^ n = ⊥)
    (ι : ℕ → Type*) (eA : ∀ k, layer J A k ≃ₗ[A] (ι k →₀ A ⧸ J))
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module (A ⧸ J) (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A (A ⧸ J) (N k)] [∀ k, Module.Flat (A ⧸ J) (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsWeaklyRegular A rs) :
    IsWeaklyRegular R rs := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have := Module.subsingleton A R
    exact isWeaklyRegular_of_subsingleton rs
  have hA0 := isWeaklyRegular_quotient_of_layers_free (M := A) (n := n) (by simp [filt, hn]) ι eA h
  refine isWeaklyRegular_of_layers (J := J) (n := n) (by simp [filt, hn]) fun k => ?_
  exact ((eR k).isWeaklyRegular_congr rs).mpr (isWeaklyRegular_of_flat _ hA0)

end Main

section Local

variable {J : Ideal A}

/-- **Lemmes 6 b) and 16 at a point.** Over a noetherian local ring `A` (the local ring
`A_𝔭` of the reading), with `J` nilpotent, if the layers of `A` and of the `A`-module `R` are flat
over `A₀ = A/J` (as generic flatness provides on `U`), every `A`-weakly regular sequence is
`R`-weakly regular. The layers of `A` are finite over the local ring `A₀`, hence free; for `R`
flatness is used as such (no finiteness on `R`, as in Lemme 16). -/
theorem isWeaklyRegular_of_gr_flat_of_isLocalRing [IsLocalRing A] [IsNoetherianRing A]
    {R : Type*} [AddCommGroup R] [Module A R] {n : ℕ} (hn : J ^ n = ⊥)
    (P : ℕ → Type*) [∀ k, AddCommGroup (P k)] [∀ k, Module (A ⧸ J) (P k)] [∀ k, Module A (P k)]
    [∀ k, IsScalarTower A (A ⧸ J) (P k)] [∀ k, Module.Flat (A ⧸ J) (P k)]
    (eA : ∀ k, layer J A k ≃ₗ[A] P k)
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module (A ⧸ J) (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A (A ⧸ J) (N k)] [∀ k, Module.Flat (A ⧸ J) (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsWeaklyRegular A rs) :
    IsWeaklyRegular R rs := by
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (by
    rintro rfl
    rw [Ideal.top_pow] at hn
    exact top_ne_bot hn)
  have : IsLocalRing (A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hfin : ∀ k, Module.Finite (A ⧸ J) (P k) := fun k =>
    have : Module.Finite A (P k) := Module.Finite.equiv (eA k)
    Module.Finite.of_restrictScalars_finite A (A ⧸ J) (P k)
  have hfree : ∀ k, Module.Free (A ⧸ J) (P k) := fun _ => Module.free_of_flat_of_isLocalRing
  exact isWeaklyRegular_of_gr hn (fun k => Module.Free.ChooseBasisIndex (A ⧸ J) (P k))
    (fun k => (eA k).trans ((Module.Free.chooseBasis (A ⧸ J) (P k)).repr.restrictScalars A))
    N eR h

/-- The same, as regular sequences: for `R` finite and nonzero and `t` in the maximal ideal, an
`A`-regular sequence is `R`-regular — so its Koszul complex, which resolves `A/(t)`, stays
acyclic after `⊗ R`, i.e. `Tor_i^A(R, A/(t)) = 0` for `i > 0` (that last step is not formalised). -/
theorem isRegular_of_gr_flat_of_isLocalRing [IsLocalRing A] [IsNoetherianRing A]
    {R : Type*} [AddCommGroup R] [Module A R] [Module.Finite A R] [Nontrivial R] {n : ℕ}
    (hn : J ^ n = ⊥)
    (P : ℕ → Type*) [∀ k, AddCommGroup (P k)] [∀ k, Module (A ⧸ J) (P k)] [∀ k, Module A (P k)]
    [∀ k, IsScalarTower A (A ⧸ J) (P k)] [∀ k, Module.Flat (A ⧸ J) (P k)]
    (eA : ∀ k, layer J A k ≃ₗ[A] P k)
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module (A ⧸ J) (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A (A ⧸ J) (N k)] [∀ k, Module.Flat (A ⧸ J) (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsRegular A rs)
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A) :
    IsRegular R rs :=
  (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
    (isWeaklyRegular_of_gr_flat_of_isLocalRing hn P eA N eR h.1)

end Local

/-!
## Page 7: a counterexample to the converse of Remarque 5 bis (local finiteness only)

Finding `94-rank-constructibility`. Remarque 5 bis claims that, under (i)–(iv) of Lemme 5
(left exactness, filtered colimits, completion at every `𝔭`, `F(M)` finite for `M` of finite
length over `A_𝔭`), condition (v) — `F` representable on a non-empty open of each `V(𝔭)` —
follows from the constructibility of `𝔭 ↦ dim F(k(𝔭))`. It does not. Take `A = k[x, y]`
(written `k[X][X]`, `x` the inner variable), distinct `a_j ∈ k`, `h_j = x − a_j`, and
`F(M) = colim(M →h M →h M → ⋯)`, the telescope `Tele` (a filtered colimit of copies of
`Hom(A, −)`, hence left exact and commuting with filtered colimits).

* `tele_atPrime_bijective`: at every prime `𝔭`, all but at most one `h_j` are units in `A_𝔭`, so
  from some stage on `F(M) ≅ M` for every `A_𝔭`-module (in particular every `Â_𝔭`-module):
  completion and local finiteness hold;
* `finrank_tele_field`: for every field `K` receiving `A` (every residue field `k(𝔭)`),
  `dim_K F(K) = 1` — the rank function is constant;
* `not_finite_tele_away`, `not_representable_away`: for every `g ≠ 0`, `F(A_g)` is not a finite
  `A_g`-module, so `F` restricted to `A_g`-modules is `Hom(Q, −)` for no finite `Q`: (v) fails
  at `𝔭 = 0`.

The general tools are `teleOf_bijective` (a telescope whose maps are eventually units is its
stage) and `exists_isUnit_of_finite` (a finite telescope of a ring along non-zero-divisors has
eventually invertible maps). Left exactness and commutation with filtered colimits are the
standard properties of filtered colimits of representables and are not restated.
-/

open Polynomial

noncomputable section

universe u

section Telescope

variable {R : Type*} [CommRing R] (c : ℕ → R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The transition maps of the telescope `M →c M →c M → ⋯` from stage `i` to stage `j`:
multiplication by `∏_{i < l ≤ j} c l`. -/
def teleMap (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M := (∏ l ∈ Finset.Ioc i j, c l) • LinearMap.id

instance teleMap_directedSystem :
    DirectedSystem (fun _ : ℕ => M) (fun i j h => teleMap c M i j h) where
  map_self i x := by simp [teleMap]
  map_map k j i hij hjk x := by
    simp only [teleMap, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm, Finset.prod_Ioc_consecutive _ hij hjk]

/-- The functor `F(M) = colim(M →c M →c M → ⋯)` of the counterexample. -/
abbrev Tele : Type _ := Module.DirectLimit (fun _ : ℕ => M) (teleMap c M)

/-- The insertion of stage `i`. -/
abbrev teleOf (i : ℕ) : M →ₗ[R] Tele c M := Module.DirectLimit.of R ℕ (fun _ => M) (teleMap c M) i

variable {c M}

theorem teleOf_eq {i j : ℕ} (h : i ≤ j) (x : M) :
    teleOf c M i x = teleOf c M j ((∏ l ∈ Finset.Ioc i j, c l) • x) := by
  rw [← Module.DirectLimit.of_f (hij := h)]; rfl

theorem teleOf_bijective {N : ℕ} (hc : ∀ l, N < l → IsUnit (c l)) : Bijective (teleOf c M N) := by
  have hP : ∀ j, IsUnit (∏ l ∈ Finset.Ioc N j, c l) := fun j =>
    IsUnit.prod_iff.2 (fun l hl => hc l (Finset.mem_Ioc.1 hl).1)
  constructor
  · intro x y hxy
    obtain ⟨j, hj, h⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
    simpa [teleMap, (hP j).smul_left_cancel] using h
  · intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    rcases le_total i N with h | h
    · exact ⟨_, (teleOf_eq h x).symm⟩
    · obtain ⟨u, hu⟩ := hP i
      refine ⟨u⁻¹ • x, ?_⟩
      rw [teleOf_eq h, ← hu]
      congr 1
      exact smul_inv_smul u x

theorem range_teleOf_mono {i j : ℕ} (h : i ≤ j) :
    LinearMap.range (teleOf c M i) ≤ LinearMap.range (teleOf c M j) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨_, (teleOf_eq h x).symm⟩

theorem exists_isUnit_of_finite (hc : ∀ l, c l ∈ nonZeroDivisors R)
    [Module.Finite R (Tele c R)] : ∃ N, ∀ l, N < l → IsUnit (c l) := by
  classical
  have key : ∀ s : Finset (Tele c R), ∃ N, ∀ z ∈ s, z ∈ LinearMap.range (teleOf c R N) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert z s _ ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
      refine ⟨max N i, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact range_teleOf_mono (le_max_right N i) ⟨x, rfl⟩
      · exact range_teleOf_mono (le_max_left N i) (hN w hw)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := Tele c R)
  obtain ⟨N, hN⟩ := key s
  have htop : LinearMap.range (teleOf c R N) = ⊤ := by
    rw [eq_top_iff, ← hs, Submodule.span_le]; exact hN
  refine ⟨N, fun l hl => ?_⟩
  obtain ⟨m, hm⟩ : teleOf c R l 1 ∈ LinearMap.range (teleOf c R N) := htop ▸ trivial
  rw [teleOf_eq hl.le] at hm
  obtain ⟨k, hk, h⟩ := Module.DirectLimit.exists_eq_of_of_eq hm
  simp only [teleMap, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h
  have hQ : (∏ j ∈ Finset.Ioc l k, c j) ∈ nonZeroDivisors R :=
    Submonoid.prod_mem _ (fun j _ => hc j)
  have h1 : (∏ j ∈ Finset.Ioc N l, c j) * m = 1 := by
    have h2 : (∏ j ∈ Finset.Ioc l k, c j) * ((∏ j ∈ Finset.Ioc N l, c j) * m - 1) = 0 := by
      rw [mul_sub, sub_eq_zero]; simpa using h
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hQ).1 _ h2)
  exact IsUnit.prod_iff.1 (IsUnit.of_mul_eq_one _ h1) l (Finset.mem_Ioc.2 ⟨hl, le_rfl⟩)

/-- If at most one index is bad, all large indices are good. -/
theorem exists_forall_gt_not {bad : ℕ → Prop} (h : ∀ i j, bad i → bad j → i = j) :
    ∃ N, ∀ l, N < l → ¬ bad l := by
  by_cases hb : ∃ j, bad j
  · obtain ⟨j, hj⟩ := hb
    exact ⟨j, fun l hl hl' => hl.ne (h j l hj hl')⟩
  · exact ⟨0, fun l _ hl => hb ⟨l, hl⟩⟩

end Telescope

section Plane

variable {k : Type*} [Field k]

/-- `x − a` in `k[x, y]`, written `k[X][X]` with `x` the inner variable. -/
abbrev hx (a : k) : k[X][X] := C (X - C a)

theorem hx_prime (a : k) : Prime (hx a) := Polynomial.prime_C_iff.2 (Polynomial.prime_X_sub_C a)

theorem hx_sub (a b : k) : hx a - hx b = C (C (b - a)) := by
  rw [← map_sub]; congr 1; rw [map_sub]; ring

theorem isUnit_hx_sub {a b : k} (hab : a ≠ b) : IsUnit (hx a - hx b) := by
  rw [hx_sub]; exact isUnit_C.2 (isUnit_C.2 (sub_ne_zero.2 hab.symm).isUnit)

/-- For `g ≠ 0`, only finitely many `x − a_j` divide `g`. -/
theorem finite_setOf_hx_dvd {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0) :
    {j | hx (a j) ∣ g}.Finite := by
  have hq : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hg
  refine ((Polynomial.finite_setOfPred_isRoot hq).preimage ha.injOn).subset fun j hj => ?_
  have := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 hj g.natDegree
  exact (Polynomial.dvd_iff_isRoot).1 this

theorem dvd_of_isUnit_away {D : Type*} [CommRing D] [IsDomain D] {g h : D} (hg : g ≠ 0)
    (hh : Prime h) (hu : IsUnit (algebraMap D (Localization.Away g) h)) : h ∣ g := by
  obtain ⟨U, hU⟩ := hu
  obtain ⟨⟨b, ⟨s, hs⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) (↑U⁻¹ : Localization.Away g)
  obtain ⟨n, rfl⟩ := hs
  simp only at e
  have hinj := IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : g ^ n = h * b := by
    apply hinj
    rw [map_mul, ← e, ← mul_assoc, ← hU, Units.mul_inv, one_mul]
  exact hh.dvd_of_dvd_pow (Dvd.intro b this.symm)

/-- `F(A_g)` is not finitely generated over `A_g` for any `g ≠ 0`. -/
theorem not_finite_tele_away {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0) :
    ¬ Module.Finite (Localization.Away g)
      (Tele (fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j))) (Localization.Away g)) := by
  intro hfin
  have : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have hinj := IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  obtain ⟨N, hN⟩ := exists_isUnit_of_finite (R := Localization.Away g)
    (c := fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j)))
    (fun l => mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (hx_prime (a l)).ne_zero))
  obtain ⟨N', hN'⟩ := (finite_setOf_hx_dvd ha hg).bddAbove
  have hl := dvd_of_isUnit_away hg (hx_prime _) (hN (max N N' + 1) (by omega))
  have := hN' hl
  omega

/-- A noetherian ring: the dual of a finite module is finite. -/
theorem finite_dual {R : Type*} [CommRing R] [IsNoetherianRing R] (Q : Type*) [AddCommGroup Q]
    [Module R Q] [Module.Finite R Q] : Module.Finite R (Q →ₗ[R] R) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R Q
  exact Module.Finite.of_injective π.dualMap (LinearMap.dualMap_injective_of_surjective hπ)

/-- Hence `F` restricted to `A_g`-modules is representable by no finite module, for any
`g ≠ 0`: the case `𝔭 = 0` of Lemma 5 (v) fails. -/
theorem not_representable_away {a : ℕ → k} (ha : Injective a) {g : k[X][X]} (hg : g ≠ 0)
    (Q : Type*) [AddCommGroup Q] [Module (Localization.Away g) Q]
    [Module.Finite (Localization.Away g) Q]
    (e : (Q →ₗ[Localization.Away g] Localization.Away g) ≃ₗ[Localization.Away g]
      Tele (fun j => algebraMap k[X][X] (Localization.Away g) (hx (a j))) (Localization.Away g)) :
    False := by
  have := finite_dual (R := Localization.Away g) Q
  exact not_finite_tele_away ha hg (Module.Finite.equiv e)

/-- Two of the `x − a_j` never vanish together in a field. -/
theorem eq_of_map_hx_eq_zero {K : Type*} [Field K] (φ : k[X][X] →+* K) {a : ℕ → k}
    (ha : Injective a) (i j : ℕ) (hi : φ (hx (a i)) = 0) (hj : φ (hx (a j)) = 0) : i = j := by
  by_contra hij
  have := (isUnit_hx_sub (ha.ne hij)).map φ
  rw [map_sub, hi, hj, sub_zero] at this
  exact not_isUnit_zero this

/-- Over any field `K` receiving `k[x, y]` (e.g. a residue field `k(𝔭)`), `F(K)` is
one-dimensional: the fibre rank of `F` is constant, equal to `1`. -/
theorem finrank_tele_field {K : Type*} [Field K] (φ : k[X][X] →+* K) {a : ℕ → k}
    (ha : Injective a) : Module.finrank K (Tele (fun j => φ (hx (a j))) K) = 1 := by
  obtain ⟨N, hN⟩ := exists_forall_gt_not (eq_of_map_hx_eq_zero φ ha)
  let e := LinearEquiv.ofBijective _ (teleOf_bijective (c := fun j => φ (hx (a j))) (M := K)
    (N := N) fun l hl => (Ne.isUnit (hN l hl)))
  rw [← e.finrank_eq, Module.finrank_self]

/-- At every prime `𝔭`, all but at most one `x − a_j` are units of `A_𝔭`, so from some stage
on `F(M) ≅ M` for every `A_𝔭`-module `M` (and every `Â_𝔭`-module): the completion and local
finiteness conditions hold. -/
theorem tele_atPrime_bijective (p : Ideal k[X][X]) [p.IsPrime] {a : ℕ → k} (ha : Injective a) :
    ∃ N, ∀ (M : Type u) [AddCommGroup M] [Module (Localization.AtPrime p) M],
      Bijective (teleOf (fun j => algebraMap k[X][X] (Localization.AtPrime p) (hx (a j))) M N) := by
  obtain ⟨N, hN⟩ := exists_forall_gt_not (bad := fun j => hx (a j) ∈ p) fun i j hi hj => by
    by_contra hij
    exact (Ideal.IsPrime.ne_top ‹_›)
      (Ideal.eq_top_of_isUnit_mem _ (p.sub_mem hi hj) (isUnit_hx_sub (ha.ne hij)))
  exact ⟨N, fun M _ _ => teleOf_bijective fun l hl =>
    (IsLocalization.AtPrime.isUnit_to_map_iff _ p _).2 (hN l hl)⟩

end Plane

end

end Grothendieck.Folder94

/-!
## Pages 8–9: the dense open of Lemme 6 for `X = S`

Finding `94-generic-tor-regular-sequences`, remainder « the dense open `U` for `X = S` ».

* `isWeaklyRegular_of_gr'`: the key step with an arbitrary `A`-algebra `B` for `A/J` and an
  arbitrary nonzero module `T` (here `A_𝔭`) for `A`;
* `isLocalizedModule_layerMap`: the layers commute with localisation,
  `grᵏ_J(S⁻¹M) = S⁻¹ grᵏ_J(M)`; with `isLocalizedModule_mk_restrictScalars`, `layerEquiv`
  identifies `grᵏ_J(M_𝔭)` with `(A/J)_q ⊗ grᵏ_J(M)` for `𝔭` over `q ∈ Spec(A/J)`;
* `exists_isOpen_dense_isWeaklyRegular'` (main theorem): for `A` noetherian, `J` nilpotent with
  `A/J` reduced (e.g. the nilradical) and `R` a finite `A`-module, there is a dense open
  `U ⊆ Spec A` such that, for `𝔭 ∈ U`, every `A_𝔭`-weakly regular sequence is `R_𝔭`-weakly
  regular. `U` is the image in `Spec A` (homeomorphic to `Spec(A/J)`) of the intersection of the
  free loci over `A/J` of the finitely many nonzero layers of `A` and `R`: open by finite
  presentation (`Module.isOpen_freeLocus`), dense because it contains every minimal prime, at
  which the reduced ring `A/J` localises to a field.

Not formalised: the Koszul step to `Tor_i^A(R, A_𝔭/(t)) = 0` (as above), and the case of `X` of
finite type over `S` (Lemme 16), which needs generic flatness.

## Page 7: the converse of Remarque 5 bis under global finiteness, module-theoretic steps

Finding `94-rank-constructibility`, remainder « the converse under global finiteness ». The
argument: on `B = (A/𝔭)_g` where the rank is `n`, the stalks `P_q` of Prop. 4 have constant fibre
rank `n` over the reduced local rings `B_q`, hence are free; `F(B)` is then finite projective, and
`F(B) ⊗ M → F(M)`, bijective at every localisation, gives `F_B ≅ Hom(F(B)^∨, −)`.

* `free_of_finrank_eq_of_isReduced`: over a reduced local ring, a finite module whose fibre rank
  at the closed point equals its rank at every minimal prime is free (no noetherian hypothesis);
* `nonempty_equiv_hom_dual`: if `P` is finitely presented with free localisations at the maximal
  ideals and `φ : P ⊗ M → N` is bijective at every maximal ideal, `P` is projective and
  `N ≅ Hom(P^∨, M)`.

Not formalised: Prop. 4 (the stalk representability, via pro-representability and Matlis
duality), and the passage from the functor `F` to these module statements (that `F(B)_q` is the
representing module `P_q`, and the naturality and localisation of `F(B) ⊗ M → F(M)`).
-/

namespace Grothendieck.Folder94

variable {A : Type*} [CommRing A]

section General

variable {J : Ideal A} (B : Type*) [CommRing B] [Algebra A B]

/-- `isWeaklyRegular_of_flat` with an arbitrary `A`-algebra `B` in place of `A/J`. -/
theorem isWeaklyRegular_of_flat' (N : Type*) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.Flat B N] {rs : List A}
    (h : IsWeaklyRegular B rs) : IsWeaklyRegular N rs := by
  rw [← isWeaklyRegular_map_algebraMap_iff B N]
  rw [← isWeaklyRegular_map_algebraMap_iff B B] at h
  exact ((TensorProduct.rid B N).isWeaklyRegular_congr _).mp
    (h.isWeaklyRegular_lTensor (M₂ := N))

/-- `isWeaklyRegular_quotient_of_layers_free` with an arbitrary `A`-algebra `B` in place of `A/J`:
if `JⁿM = 0`, `M ≠ 0` and the layers of `M` are free over `B`, every `M`-weakly regular sequence
is `B`-weakly regular (same proof). -/
theorem isWeaklyRegular_of_layers_free' {M : Type*} [AddCommGroup M] [Module A M]
    [Nontrivial M] {n : ℕ} (hn : filt J M n = ⊥) (ι : ℕ → Type*)
    (e : ∀ k, layer J M k ≃ₗ[A] (ι k →₀ B)) {rs : List A} (h : IsWeaklyRegular M rs) :
    IsWeaklyRegular B rs := by
  classical
  have hex : ∃ k, filt J M (k + 1) = ⊥ :=
    ⟨n, eq_bot_iff.mpr ((filt_antitone (Nat.le_succ n)).trans hn.le)⟩
  set m := Nat.find hex with hmdef
  have hm : filt J M (m + 1) = ⊥ := Nat.find_spec hex
  have hm0 : filt J M m ≠ ⊥ := by
    intro h0
    rcases m.eq_zero_or_pos with hz | hs
    · rw [hz, filt_zero] at h0
      exact top_ne_bot h0
    · have := Nat.find_min' hex (m := m - 1) (by rwa [Nat.sub_add_cancel hs])
      omega
  have hcomap : (filt J M (m + 1)).comap (filt J M m).subtype = ⊥ := by
    rw [hm, comap_bot, ker_subtype]
  let eL : ↥(filt J M m) ≃ₗ[A] (ι m →₀ B) :=
    (quotEquivOfEqBot _ hcomap).symm.trans (e m)
  have hne : Nonempty (ι m) := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have : Subsingleton ↥(filt J M m) := eL.toEquiv.subsingleton
    exact hm0 Submodule.eq_bot_of_subsingleton
  obtain ⟨i⟩ := hne
  induction rs using List.reverseRecOn with
  | nil => exact IsWeaklyRegular.nil _ _
  | append_singleton rs y ih =>
    rw [isWeaklyRegular_append_iff] at h
    have h0 := ih h.1
    have hlay : ∀ k, IsWeaklyRegular (layer J M k) rs := fun k =>
      ((e k).isWeaklyRegular_congr rs).mpr (isWeaklyRegular_of_flat' B _ h0)
    have hq : IsWeaklyRegular (M ⧸ filt J M m) rs :=
      isWeaklyRegular_quotient_filt m fun k _ => hlay k
    have hf := Submodule.injective_subtype (filt J M m)
    have hfg := LinearMap.exact_subtype_mkQ (filt J M m)
    have hg := (filt J M m).mkQ_surjective
    have hinj := injective_mapQ_of_exact hf hfg hg hq
    refine isWeaklyRegular_of_retract (i := Finsupp.lsingle (R := A) i)
      (p := Finsupp.lapply (R := A) i) (by ext; simp) ((eL.isWeaklyRegular_congr _).mp ?_)
    rw [isWeaklyRegular_append_iff]
    refine ⟨(isWeaklyRegular_iff_of_exact hf hfg hg hq).mpr h.1, ?_⟩
    have h2 := h.2
    rw [isWeaklyRegular_singleton_iff] at h2 ⊢
    exact h2.of_injective _ hinj

/-- The key step of Lemmes 6 b) and 16 with an arbitrary `A`-algebra `B` in place of `A/J` and an
arbitrary nonzero `A`-module `T` in place of `A`: if `JⁿT = JⁿR = 0`, the layers of `T` are free
over `B` and those of `R` flat over `B`, every `T`-weakly regular sequence is `R`-weakly regular. -/
theorem isWeaklyRegular_of_gr' {T R : Type*} [AddCommGroup T] [Module A T] [Nontrivial T]
    [AddCommGroup R] [Module A R] {n : ℕ} (hT : filt J T n = ⊥) (hR : filt J R n = ⊥)
    (ι : ℕ → Type*) (eT : ∀ k, layer J T k ≃ₗ[A] (ι k →₀ B))
    (N : ℕ → Type*) [∀ k, AddCommGroup (N k)] [∀ k, Module B (N k)] [∀ k, Module A (N k)]
    [∀ k, IsScalarTower A B (N k)] [∀ k, Module.Flat B (N k)]
    (eR : ∀ k, layer J R k ≃ₗ[A] N k) {rs : List A} (h : IsWeaklyRegular T rs) :
    IsWeaklyRegular R rs :=
  isWeaklyRegular_of_layers hR fun k => ((eR k).isWeaklyRegular_congr rs).mpr
    (isWeaklyRegular_of_flat' B _ (isWeaklyRegular_of_layers_free' B hT ι eT h))

end General

section LocalizeLayers

variable (J : Ideal A) (S : Submonoid A) {M N : Type*} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) [IsLocalizedModule S f]

/-- `Jᵏ(S⁻¹M)` is the localisation of `JᵏM`. -/
theorem filt_eq_localized₀ (k : ℕ) : filt J N k = (filt J M k).localized₀ S f := by
  rw [filt, localized₀_smul, localized₀_top]

/-- The map `grᵏ_J(M) → grᵏ_J(N)` induced by a localisation `f : M → N = S⁻¹M`. -/
def layerMap (k : ℕ) : layer J M k →ₗ[A] layer J N k :=
  mapQ _ _ (f.restrict fun x hx => by
    rw [filt_eq_localized₀ J S f]; exact ⟨x, hx, 1, by simp⟩) fun x hx => by
    simp only [mem_comap, subtype_apply, LinearMap.restrict_apply] at hx ⊢
    rw [filt_eq_localized₀ J S f]; exact ⟨x, hx, 1, by simp⟩

variable {J S}

include f in
theorem mem_filt_of_smul {k : ℕ} (s : S) {y : N} (h : s • y ∈ filt J N k) : y ∈ filt J N k := by
  rw [filt_eq_localized₀ J S f] at h ⊢
  obtain ⟨m, hm, t, e⟩ := h
  refine ⟨m, hm, s * t, ?_⟩
  rw [IsLocalizedModule.mk'_eq_iff, mul_comm, mul_smul, ← e, IsLocalizedModule.mk'_cancel']

include f in
theorem exists_smul_eq_of_mem_filt {k : ℕ} (s : S) {y : N} (h : y ∈ filt J N k) :
    ∃ z ∈ filt J N k, s • z = y := by
  rw [filt_eq_localized₀ J S f] at h ⊢
  obtain ⟨m, hm, t, rfl⟩ := h
  exact ⟨_, ⟨m, hm, s * t, rfl⟩, by
    rw [Submonoid.smul_def, ← IsLocalizedModule.mk'_smul, ← Submonoid.smul_def,
      IsLocalizedModule.mk'_cancel_left]⟩

/-- **The layers commute with localisation**: `grᵏ_J(S⁻¹M) = S⁻¹ grᵏ_J(M)`. -/
instance isLocalizedModule_layerMap (k : ℕ) : IsLocalizedModule S (layerMap J S f k) where
  map_units s := by
    refine (Module.End.isUnit_iff _).mpr ⟨fun a b e => ?_, fun b => ?_⟩
    · rw [← sub_eq_zero] at e ⊢
      rw [← map_sub] at e
      generalize a - b = c at e
      induction c using Submodule.Quotient.induction_on with
      | H y =>
        rw [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.mk_eq_zero] at e
        rw [Submodule.Quotient.mk_eq_zero]
        exact mem_filt_of_smul f s e
    · induction b using Submodule.Quotient.induction_on with
      | H y =>
        obtain ⟨z, hz, e⟩ := exists_smul_eq_of_mem_filt f s y.2
        exact ⟨Submodule.Quotient.mk ⟨z, hz⟩, congrArg Submodule.Quotient.mk (Subtype.ext e)⟩
  surj y := by
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨y, hy⟩ := y
      rw [filt_eq_localized₀ J S f] at hy
      obtain ⟨m, hm, t, rfl⟩ := hy
      exact ⟨(Submodule.Quotient.mk ⟨m, hm⟩, t), congrArg Submodule.Quotient.mk
        (Subtype.ext (IsLocalizedModule.mk'_cancel' f m t))⟩
  exists_of_eq {a b} e := by
    induction a using Submodule.Quotient.induction_on with
    | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      rw [layerMap, mapQ_apply, mapQ_apply, Submodule.Quotient.eq] at e
      simp only [mem_comap, subtype_apply, AddSubgroupClass.coe_sub,
        LinearMap.restrict_apply, ← map_sub] at e
      rw [filt_eq_localized₀ J S f] at e
      obtain ⟨x, hx, t, e⟩ := e
      rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at e
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) e
      refine ⟨c * t, ?_⟩
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      simp only [mem_comap, subtype_apply, ← smul_sub, mul_smul]
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, AddSubgroupClass.coe_sub, ← hc]
      exact (filt J M (k + 1)).smul_of_tower_mem c hx

end LocalizeLayers

section GenericOpen

open Module PrimeSpectrum TensorProduct Pointwise

variable {J : Ideal A}

/-- `J` kills the layers. -/
theorem isTorsionBySet_layer (M : Type*) [AddCommGroup M] [Module A M] (k : ℕ) :
    IsTorsionBySet A (layer J M k) J := by
  rintro x ⟨a, ha⟩
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_comap,
      subtype_apply, Submodule.coe_smul_of_tower, filt, pow_succ', Submodule.mul_smul]
    exact smul_mem_smul ha y.2

/-- The layers are `A/J`-modules. -/
@[instance_reducible]
def layerModule (M : Type*) [AddCommGroup M] [Module A M] (k : ℕ) :
    Module (A ⧸ J) (layer J M k) :=
  (isTorsionBySet_layer M k).module

attribute [local instance] layerModule

instance (M : Type*) [AddCommGroup M] [Module A M] (k : ℕ) :
    IsScalarTower A (A ⧸ J) (layer J M k) :=
  IsTorsionBySet.isScalarTower _

/-- The base change `L → (A/J)_q ⊗ L` is, over `A`, a localisation at the inverse image of `q`. -/
instance isLocalizedModule_mk_restrictScalars (q : PrimeSpectrum (A ⧸ J)) (L : Type*)
    [AddCommGroup L] [Module A L] [Module (A ⧸ J) L] [IsScalarTower A (A ⧸ J) L] :
    IsLocalizedModule (q.asIdeal.comap (Ideal.Quotient.mk J)).primeCompl
      ((TensorProduct.mk (A ⧸ J) (Localization.AtPrime q.asIdeal) L 1).restrictScalars A) where
  map_units s := by
    have := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := q.asIdeal.primeCompl)
      (TensorProduct.mk (A ⧸ J) (Localization.AtPrime q.asIdeal) L 1) ⟨Ideal.Quotient.mk J s, s.2⟩)
    exact (Module.End.isUnit_iff _).mpr (by
      convert this using 1; ext x; exact (algebraMap_smul (A ⧸ J) (s : A) x).symm)
  surj y := by
    obtain ⟨⟨x, t, ht⟩, e⟩ := IsLocalizedModule.surj q.asIdeal.primeCompl
      (TensorProduct.mk (A ⧸ J) (Localization.AtPrime q.asIdeal) L 1) y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact ⟨(x, ⟨t, ht⟩), (algebraMap_smul (A ⧸ J) t y).symm.trans e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨c, hc⟩, e⟩ := IsLocalizedModule.exists_of_eq (S := q.asIdeal.primeCompl)
      (f := TensorProduct.mk (A ⧸ J) (Localization.AtPrime q.asIdeal) L 1) e
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨⟨c, hc⟩, ?_⟩
    change c • x₁ = c • x₂
    rw [← algebraMap_smul (A ⧸ J) c x₁, ← algebraMap_smul (A ⧸ J) c x₂]
    exact e

/-- Over a reduced ring every minimal prime lies in the free locus of every module. -/
theorem mem_freeLocus_of_mem_minimalPrimes {R L : Type*} [CommRing R] [IsReduced R]
    [AddCommGroup L] [Module R L] (q : PrimeSpectrum R) (hq : q.asIdeal ∈ minimalPrimes R) :
    q ∈ freeLocus R L := by
  have := Ring.KrullDimLE.of_isLocalization q.asIdeal hq (Localization.AtPrime q.asIdeal)
  let : Field (Localization.AtPrime q.asIdeal) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact Module.Free.of_divisionRing _ _

/-- A set of primes containing every minimal prime is dense. -/
theorem dense_of_minimalPrimes_subset {R : Type*} [CommRing R] {V : Set (PrimeSpectrum R)}
    (hV : ∀ q : PrimeSpectrum R, q.asIdeal ∈ minimalPrimes R → q ∈ V) : Dense V := fun p => by
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
  exact ((le_iff_specializes ⟨q, hq.1.1⟩ p).mp hq').mem_closed isClosed_closure
    (subset_closure (hV ⟨q, hq.1.1⟩ hq))

/-- At a point of the free locus of the nonzero layers, all layers are free. -/
theorem free_tensor_layer (q : PrimeSpectrum (A ⧸ J)) {M : Type*} [AddCommGroup M] [Module A M]
    {n : ℕ} (hM : filt J M n = ⊥) (hq : ∀ k < n, q ∈ freeLocus (A ⧸ J) (layer J M k)) (k : ℕ) :
    Module.Free (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[A ⧸ J] layer J M k) := by
  rcases lt_or_ge k n with hk | hk
  · exact (mem_freeLocus_iff_tensor q _).1 (hq k hk)
  · have : Subsingleton (filt J M k) := by
      rw [eq_bot_iff.2 ((filt_antitone hk).trans hM.le)]; infer_instance
    infer_instance

/-- **Compatibility of the layers with localisation.** If `N = M_𝔭` with `𝔭` the inverse image
of `q ∈ Spec(A/J)`, then `grᵏ_J(N) ≅ (A/J)_q ⊗ grᵏ_J(M)`. -/
noncomputable def layerEquiv (q : PrimeSpectrum (A ⧸ J)) {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N)
    [IsLocalizedModule (q.asIdeal.comap (Ideal.Quotient.mk J)).primeCompl f] (k : ℕ) :
    layer J N k ≃ₗ[A] Localization.AtPrime q.asIdeal ⊗[A ⧸ J] layer J M k :=
  IsLocalizedModule.linearEquiv (q.asIdeal.comap (Ideal.Quotient.mk J)).primeCompl
    (layerMap J (q.asIdeal.comap (Ideal.Quotient.mk J)).primeCompl f k)
    ((TensorProduct.mk (A ⧸ J) (Localization.AtPrime q.asIdeal) (layer J M k) 1).restrictScalars A)

/-- Weak regularity only depends on the sequence up to units. -/
theorem isWeaklyRegular_of_forall₂_associated {B M : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] {rs rs' : List B} (h : List.Forall₂ Associated rs rs')
    (hM : IsWeaklyRegular M rs) : IsWeaklyRegular M rs' := by
  induction h generalizing M with
  | nil => exact hM
  | @cons a b _ _ hab _ ih =>
    obtain ⟨u, rfl⟩ := hab
    rw [isWeaklyRegular_cons_iff] at hM ⊢
    have heq : (a * (u : B)) • (⊤ : Submodule B M) = a • ⊤ := by
      rw [mul_smul]
      congr 1
      refine eq_top_iff.2 fun x _ => (Submodule.mem_smul_pointwise_iff_exists x (u : B) ⊤).2
        ⟨(↑u⁻¹ : B) • x, Submodule.mem_top, ?_⟩
      rw [smul_smul, u.mul_inv, one_smul]
    exact ⟨hM.1.mul (u.isUnit.isSMulRegular M),
      ((Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr _).mpr (ih hM.2)⟩

variable [IsNoetherianRing A]

/-- The layers of a finite module are finite over `A/J`, hence finitely presented. -/
instance (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] (k : ℕ) :
    FinitePresentation (A ⧸ J) (layer J M k) :=
  have := Module.Finite.of_restrictScalars_finite A (A ⧸ J) (layer J M k)
  finitePresentation_of_finite _ _

/-- **Lemme 6, the dense open, for `X = S`.** Let `A` be noetherian, `J` a nilpotent ideal with
`A/J` reduced (e.g. the nilradical), and `R` a finite `A`-module. There is a dense open
`U ⊆ Spec A` such that at every `𝔭 ∈ U` every sequence of `A` weakly regular on `A_𝔭` is weakly
regular on `R_𝔭`. `U` is the locus where the finitely many nonzero layers of `A` and of `R`
are free over `A/J` (open by finite presentation, dense since it contains the minimal primes,
at which `A/J` localises to a field). -/
theorem exists_isOpen_dense_isWeaklyRegular {n : ℕ} (hn : J ^ n = ⊥) [IsReduced (A ⧸ J)]
    (R : Type*) [AddCommGroup R] [Module A R] [Module.Finite A R] :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ Dense U ∧ ∀ 𝔭 ∈ U, ∀ rs : List A,
      IsWeaklyRegular (Localization.AtPrime 𝔭.asIdeal) rs →
        IsWeaklyRegular (LocalizedModule 𝔭.asIdeal.primeCompl R) rs := by
  have hJ : J ≤ nilradical A := fun x hx => ⟨n, by simpa [hn] using Ideal.pow_mem_pow hx n⟩
  let h := (isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorphOfSurjective
    (comap_quotientMk_bijective_of_le_nilradical hJ).2
  let V : Set (PrimeSpectrum (A ⧸ J)) :=
    ⋂ k ∈ Finset.range n, freeLocus (A ⧸ J) (layer J A k) ∩ freeLocus (A ⧸ J) (layer J R k)
  have hV : IsOpen V := isOpen_biInter_finset fun k _ => isOpen_freeLocus.inter isOpen_freeLocus
  refine ⟨h '' V, h.isOpenMap _ hV, h.surjective.denseRange.dense_image h.continuous
    (dense_of_minimalPrimes_subset fun q hq => Set.mem_iInter₂.2 fun k _ =>
      ⟨mem_freeLocus_of_mem_minimalPrimes q hq, mem_freeLocus_of_mem_minimalPrimes q hq⟩), ?_⟩
  rintro _ ⟨q, hq, rfl⟩ rs hrs
  have hq' k (hk : k < n) := Set.mem_iInter₂.1 hq k (Finset.mem_range.2 hk)
  have := free_tensor_layer q (M := A) (by simp [filt, hn]) fun k hk => (hq' k hk).1
  have := free_tensor_layer q (M := R) (by simp [filt, hn]) fun k hk => (hq' k hk).2
  have : IsLocalizedModule (q.asIdeal.comap (Ideal.Quotient.mk J)).primeCompl
      (Algebra.linearMap A (Localization.AtPrime (h q).asIdeal)) :=
    inferInstanceAs (IsLocalizedModule (h q).asIdeal.primeCompl _)
  have : IsLocalizedModule (q.asIdeal.comap (Ideal.Quotient.mk J)).primeCompl
      (LocalizedModule.mkLinearMap (h q).asIdeal.primeCompl R) :=
    inferInstanceAs (IsLocalizedModule (h q).asIdeal.primeCompl _)
  exact isWeaklyRegular_of_gr' (Localization.AtPrime q.asIdeal) (J := J) (n := n)
    (by simp [filt, hn]) (by simp [filt, hn]) _
    (fun k => (layerEquiv q (Algebra.linearMap A (Localization.AtPrime (h q).asIdeal)) k).trans
      ((Module.Free.chooseBasis _ _).repr.restrictScalars A))
    (fun k => Localization.AtPrime q.asIdeal ⊗[A ⧸ J] layer J R k)
    (layerEquiv q (LocalizedModule.mkLinearMap (h q).asIdeal.primeCompl R)) hrs

/-- **Lemme 6 for `X = S`, as stated.** The same dense open `U`, for every `A_𝔭`-weakly regular
sequence of `A_𝔭` (each term is a unit times the image of an element of `A`). -/
theorem exists_isOpen_dense_isWeaklyRegular' {n : ℕ} (hn : J ^ n = ⊥) [IsReduced (A ⧸ J)]
    (R : Type*) [AddCommGroup R] [Module A R] [Module.Finite A R] :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ Dense U ∧
      ∀ 𝔭 ∈ U, ∀ rs : List (Localization.AtPrime 𝔭.asIdeal),
        IsWeaklyRegular (Localization.AtPrime 𝔭.asIdeal) rs →
          IsWeaklyRegular (LocalizedModule 𝔭.asIdeal.primeCompl R) rs := by
  obtain ⟨U, hU, hd, H⟩ := exists_isOpen_dense_isWeaklyRegular hn R
  refine ⟨U, hU, hd, fun 𝔭 h𝔭 rs hrs => ?_⟩
  let S := 𝔭.asIdeal.primeCompl
  have hass : List.Forall₂ Associated rs
      ((rs.map fun x => (IsLocalization.sec S x).1).map (algebraMap A _)) := by
    rw [List.map_map, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun x _ =>
      ⟨(IsLocalization.map_units _ (IsLocalization.sec S x).2).unit, IsLocalization.sec_spec S x⟩
  have h1 := isWeaklyRegular_of_forall₂_associated hass hrs
  rw [isWeaklyRegular_map_algebraMap_iff] at h1
  exact isWeaklyRegular_of_forall₂_associated (hass.flip.imp fun _ _ => Associated.symm)
    ((isWeaklyRegular_map_algebraMap_iff _ _ _).2 (H 𝔭 h𝔭 _ h1))

end GenericOpen

section Converse

open Module TensorProduct IsLocalRing

/-- **Rem. 5 bis, constant fibre rank over a reduced ring.** Over a reduced local ring `B`, a
finite module `P` with `dim_{B_𝔮}(B_𝔮 ⊗ P) = dim_k(k ⊗ P)` at every minimal prime `𝔮` (where
`B_𝔮` is a field) is free. A basis of `k ⊗ P` lifts to a surjection `Bⁿ → P`; at each minimal
`𝔮` it becomes a surjection between `B_𝔮`-spaces of the same dimension, hence injective, so the
coordinates of a kernel element lie in every minimal prime, i.e. in the nilradical `0`. -/
theorem free_of_finrank_eq_of_isReduced {B P : Type*} [CommRing B] [IsLocalRing B] [IsReduced B]
    [AddCommGroup P] [Module B P] [Module.Finite B P]
    (h : ∀ 𝔮 : PrimeSpectrum B, 𝔮.asIdeal ∈ minimalPrimes B →
      finrank (Localization.AtPrime 𝔮.asIdeal) (Localization.AtPrime 𝔮.asIdeal ⊗[B] P) =
        finrank (ResidueField B) (ResidueField B ⊗[B] P)) :
    Module.Free B P := by
  let b := Module.finBasis (ResidueField B) (ResidueField B ⊗[B] P)
  choose v hv using fun i => TensorProduct.mk_surjective B P (ResidueField B)
    Ideal.Quotient.mk_surjective (b i)
  let f := Fintype.linearCombination B v
  have hf : Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_eq_top_of_tmul_eq_basis v b hv
  have hinj : Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    ext i
    have hmem : x i ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro 𝔮 h𝔮
      have := h𝔮.1.1
      have := Ring.KrullDimLE.of_isLocalization 𝔮 h𝔮 (Localization.AtPrime 𝔮)
      let : Field (Localization.AtPrime 𝔮) := Ring.KrullDimLE.isField_of_isReduced.toField
      have hfq : Injective (f.baseChange (Localization.AtPrime 𝔮)) := by
        refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2
          (LinearMap.lTensor_surjective _ hf)
        rw [finrank_baseChange, h ⟨𝔮, h𝔮.1.1⟩ h𝔮, finrank_fin_fun, Module.finrank_eq_card_basis b,
          Fintype.card_fin]
      have h1 : (1 : Localization.AtPrime 𝔮) ⊗ₜ[B] x = 0 :=
        hfq (by rw [LinearMap.baseChange_tmul, hx, tmul_zero, map_zero])
      have h2 := congrFun (congrArg (piScalarRight B B (Localization.AtPrime 𝔮) (Fin _)) h1) i
      simp only [piScalarRight_apply, piScalarRightHom_tmul, map_zero, Pi.zero_apply] at h2
      rw [Algebra.smul_def, mul_one, IsLocalization.map_eq_zero_iff (Ideal.primeCompl 𝔮)] at h2
      obtain ⟨⟨m, hm⟩, e⟩ := h2
      exact (h𝔮.1.1.mem_or_mem (e ▸ 𝔮.zero_mem)).resolve_left hm
    simpa [nilradical_eq_zero] using hmem
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hf⟩)

/-- **Rem. 5 bis, the last step.** If `P` (here `F(B)`) is finitely presented with free
localisations at the maximal ideals, and `φ : P ⊗ M → N` (here `F(B) ⊗ M → F(M)`) is bijective
at every maximal ideal, then `P` is projective and `N ≅ Hom(P^∨, M)`. -/
theorem nonempty_equiv_hom_dual {B P M N : Type*} [CommRing B] [AddCommGroup P] [Module B P]
    [Module.FinitePresentation B P] [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (hP : ∀ (m : Ideal B) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl P))
    (φ : P ⊗[B] M →ₗ[B] N)
    (hφ : ∀ (m : Ideal B) [m.IsMaximal], Bijective (LocalizedModule.map m.primeCompl φ)) :
    Module.Projective B P ∧ Nonempty (N ≃ₗ[B] (Dual B P →ₗ[B] M)) := by
  have : Module.Projective B P := projective_of_localization_maximal fun m _ => inferInstance
  exact ⟨this, ⟨(LinearEquiv.ofBijective φ (bijective_of_localized_maximal φ hφ)).symm ≪≫ₗ
    TensorProduct.congr (evalEquiv B P) (LinearEquiv.refl B M) ≪≫ₗ
    dualTensorHomEquiv B (Dual B P) M⟩⟩

end Converse

end Grothendieck.Folder94
