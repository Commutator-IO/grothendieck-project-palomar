module

public import Mathlib
public import Grothendieck.Folder94
public import StacksFrontier.RingTheory.Flat.GenericFlatness

@[expose] public section


/-!
# Folder 94, page 19 (Lemme 16): the dense open for `X` of finite type over `S`

`Grothendieck/Folder94.lean` builds, for `S = Spec A` noetherian and `R` a finite `A`-module,
the dense open `U ⊆ S` of Lemme 6 on which every `A_𝔭`-regular sequence is `R_𝔭`-regular
(`exists_isOpen_dense_isWeaklyRegular'`), and leaves out the case of Lemme 16, where `R` is a
coherent module on an `X = Spec B` of finite type over `S`: there the layers `grᵏ_J(R)` are no
longer finite over `A₀ = A/J`, and one needs generic flatness.

This file supplies it with the vendored AxiomMath/Stacks theorem
`Algebra.exists_isOpen_dense_isFinitePresentationFreeAway` (Stacks tag 051Z, file
`StacksFrontier/RingTheory/Flat/GenericFlatness.lean`): over a *reduced* ring `A₀`, for a finite
type `A₀`-algebra `S` and a finite `S`-module `M`, the points of `Spec A₀` near which `M` becomes
free form a dense open. The survey of 2026-11-15 named the noetherian-domain form 051R
(`Module.exists_ne_zero_free_localizedModule_away`) with a passage from domains to the reduced
ring through its minimal primes; the library's own reduced form 051Z does that passage, and its
import closure contains 051R, so it is used directly.

**What is proved.**
* `exists_isOpen_dense_subset_freeLocus`: generic freeness over a reduced ring, in the form of a
  dense open contained in Mathlib's `Module.freeLocus` (from 051Z, by comparing Stacks'
  localisation `S_f ⊗_S M` with Mathlib's `LocalizedModule`);
* `filt_map_eq`, `layerMapEquiv`: for a `B`-module `R`, the `J`-adic filtration of `R` as an
  `A`-module is the `JB`-adic filtration as a `B`-module, so the layer `grᵏ_J(R)` is, as an
  `A`-module, the layer `grᵏ_{JB}(R)` of `B`-modules, a `B/JB`-module;
* `exists_isOpen_dense_subset_freeLocus_layer`: for `B` of finite type over `A` noetherian and
  `R` a finite `B`-module, each layer `grᵏ_J(R)` is free over `A₀` near the points of a dense
  open of `Spec A₀`;
* `exists_isOpen_dense_isWeaklyRegular_of_finiteType`,
  `exists_isOpen_dense_isWeaklyRegular_of_finiteType'` (main theorems, **Lemme 16**): for `A`
  noetherian, `J` nilpotent with `A/J` reduced, `B` an `A`-algebra of finite type and `R` a
  finite `B`-module, there is a dense open `U ⊆ Spec A` such that at every `𝔭 ∈ U` every
  `A_𝔭`-weakly regular sequence is weakly regular on `R_𝔭`.

As in `Folder94.lean`, the open is the intersection of finitely many dense opens of
`Spec A₀ ≅ Spec A`: the free loci of the nonzero layers of `A` (finite over `A₀`) and, for each
nonzero layer of `R`, the generic freeness open of 051Z. The step from weak regularity on `R_𝔭`
to the vanishing of `Tor` is `Folder94Koszul.lean`'s, with the same caveat.
-/

open RingTheory.Sequence Submodule Function Module PrimeSpectrum TensorProduct

namespace Grothendieck.Folder94

section GenericFreeness

/-- **Generic freeness over a reduced ring** (from Stacks 051Z). Let `R₀` be a reduced ring, `S` a
finite type `R₀`-algebra and `M` a finite `S`-module. There is a dense open `U ⊆ Spec R₀` on which
`M` is free: `M_𝔭` is a free `(R₀)_𝔭`-module for every `𝔭 ∈ U`. -/
theorem exists_isOpen_dense_subset_freeLocus {R₀ S M : Type*} [CommRing R₀] [IsReduced R₀]
    [CommRing S] [Algebra R₀ S] [Algebra.FiniteType R₀ S] [AddCommGroup M] [Module S M]
    [Module.Finite S M] [Module R₀ M] [IsScalarTower R₀ S M] :
    ∃ U : Set (PrimeSpectrum R₀), IsOpen U ∧ Dense U ∧ U ⊆ freeLocus R₀ M := by
  obtain ⟨U, hU, hd, H⟩ := Algebra.exists_isOpen_dense_isFinitePresentationFreeAway
    (R := R₀) (S := S) (M := M)
  refine ⟨U, hU, hd, fun u hu => ?_⟩
  obtain ⟨f, huf, -, hf⟩ := H u hu
  let Sf := Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))
  have hF : Module.Free (Localization.Away f) (Sf ⊗[S] M) := hf.2.2.2
  -- `M → S_f ⊗_S M` is a localisation of `M` at the powers of `f`, over `R₀`
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid S (Submonoid.powers f))
      (TensorProduct.mk S Sf M 1) := inferInstance
  have hloc : IsLocalizedModule (Submonoid.powers f)
      ((TensorProduct.mk S Sf M 1).restrictScalars R₀) :=
    IsLocalizedModule.restrictScalars _ _
  let e : LocalizedModule (Submonoid.powers f) M ≃ₗ[R₀] Sf ⊗[S] M :=
    IsLocalizedModule.linearEquiv (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      ((TensorProduct.mk S Sf M 1).restrictScalars R₀)
  have hfree : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
    Module.Free.of_equiv
      (e.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)).symm
  -- `u` comes from a prime of `R₀_f`, at which the localisation of the free `M_f` is free
  have hu' : u ∈ Set.range (comap (algebraMap R₀ (Localization.Away f))) := by
    rw [localization_away_comap_range (Localization.Away f) f]; exact huf
  obtain ⟨p, rfl⟩ := hu'
  have hp : p ∈ freeLocus (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M) :=
    (mem_freeLocus_iff_tensor p (Localization.AtPrime p.asIdeal)).2 inferInstance
  rw [freeLocus_localization] at hp
  exact hp

end GenericFreeness

section Layers

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
  {R : Type*} [AddCommGroup R] [Module A R] [Module B R] [IsScalarTower A B R]

/-- The `J`-adic filtration of a `B`-module, taken over `A`, is its `JB`-adic filtration. -/
theorem filt_map_eq (J : Ideal A) (k : ℕ) :
    (filt (J.map (algebraMap A B)) R k).restrictScalars A = filt J R k := by
  rw [filt, filt, ← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem mem_filt_map_iff (J : Ideal A) (k : ℕ) (x : R) :
    x ∈ filt (J.map (algebraMap A B)) R k ↔ x ∈ filt J R k := by
  rw [← filt_map_eq (B := B) J k, Submodule.restrictScalars_mem]

/-- The identity of `R` identifies `JᵏR` over `A` with `(JB)ᵏR` over `B`, `A`-linearly. -/
def filtMapEquiv (J : Ideal A) (k : ℕ) :
    ↥(filt J R k) ≃ₗ[A] ↥(filt (J.map (algebraMap A B)) R k) where
  toFun x := ⟨x.1, (mem_filt_map_iff (B := B) J k x.1).2 x.2⟩
  invFun y := ⟨y.1, (mem_filt_map_iff (B := B) J k y.1).1 y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The layers of a `B`-module.** As an `A`-module, `grᵏ_J(R)` is the layer `grᵏ_{JB}(R)` of
`R` as a `B`-module, which is a `B/JB`-module. -/
noncomputable def layerMapEquiv (J : Ideal A) (k : ℕ) :
    layer J R k ≃ₗ[A] layer (J.map (algebraMap A B)) R k :=
  (Submodule.Quotient.equiv _ _ (filtMapEquiv J k) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨x, hx, he⟩
      obtain rfl : x.1 = y := congrArg Subtype.val he
      exact (mem_filt_map_iff (B := B) J (k + 1) x.1).2 hx
    · intro h
      exact ⟨⟨y, (mem_filt_map_iff (B := B) J k y).1 hy⟩,
        (mem_filt_map_iff (B := B) J (k + 1) y).1 h, rfl⟩)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

end Layers

section Main

variable {A : Type*} [CommRing A] {J : Ideal A}

attribute [local instance] layerModule

/-- A finite intersection of dense opens is dense. -/
theorem dense_biInter_range {X : Type*} [TopologicalSpace X] (s : ℕ → Set X)
    (ho : ∀ k, IsOpen (s k)) (hd : ∀ k, Dense (s k)) (n : ℕ) :
    Dense (⋂ k ∈ Finset.range n, s k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biInter_insert]
    exact (hd n).inter_of_isOpen_left ih (ho n)

variable (B : Type*) [CommRing B] [Algebra A B] (R : Type*) [AddCommGroup R] [Module A R]
  [Module B R] [IsScalarTower A B R]

/-- **The layers of `R` are generically free over `A₀`.** Let `A` be noetherian with `A/J`
reduced, `B` a finite type `A`-algebra and `R` a finite `B`-module. For every `k` there is a
dense open of `Spec(A/J)` on which `grᵏ_J(R)` is free over `A/J`. -/
theorem exists_isOpen_dense_subset_freeLocus_layer [IsNoetherianRing A] [IsReduced (A ⧸ J)]
    [Algebra.FiniteType A B] [Module.Finite B R] (k : ℕ) :
    ∃ W : Set (PrimeSpectrum (A ⧸ J)), IsOpen W ∧ Dense W ∧
      W ⊆ freeLocus (A ⧸ J) (layer J R k) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let JB := J.map (algebraMap A B)
  let L := layer JB R k
  -- `L` is a finite module over `S = B/JB`, a finite type `A/J`-algebra
  have : Module.Finite (B ⧸ JB) L := inferInstance
  have : Algebra.FiniteType A (B ⧸ JB) := Algebra.FiniteType.trans (S := B) inferInstance
    inferInstance
  have : Algebra.FiniteType (A ⧸ J) (B ⧸ JB) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ J) (B ⧸ JB)
  let : Module (A ⧸ J) L := Module.compHom L (algebraMap (A ⧸ J) (B ⧸ JB))
  have : IsScalarTower (A ⧸ J) (B ⧸ JB) L :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨W, hW, hd, hsub⟩ := exists_isOpen_dense_subset_freeLocus (R₀ := A ⧸ J) (S := B ⧸ JB)
    (M := L)
  refine ⟨W, hW, hd, hsub.trans (le_of_eq ?_)⟩
  -- transport along the `A`-linear identification of the layers, which is `A/J`-linear
  let e := layerMapEquiv (B := B) (R := R) J k
  refine (freeLocus_congr
    { e with
      map_smul' := fun c x => ?_ }).symm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  change e (Ideal.Quotient.mk J a • x) = (algebraMap (A ⧸ J) (B ⧸ JB) (Ideal.Quotient.mk J a)) • e x
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, map_smul,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B (B ⧸ JB),
    algebraMap_smul, algebraMap_smul]

variable [IsNoetherianRing A]

/-- **Lemme 16, the dense open, for `X` of finite type over `S`.** Let `A` be noetherian, `J` a
nilpotent ideal with `A/J` reduced (e.g. the nilradical), `B` an `A`-algebra of finite type and
`R` a finite `B`-module. There is a dense open `U ⊆ Spec A` such that at every `𝔭 ∈ U` every
sequence of `A` weakly regular on `A_𝔭` is weakly regular on `R_𝔭`. -/
theorem exists_isOpen_dense_isWeaklyRegular_of_finiteType {n : ℕ} (hn : J ^ n = ⊥)
    [IsReduced (A ⧸ J)] [Algebra.FiniteType A B] [Module.Finite B R] :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ Dense U ∧ ∀ 𝔭 ∈ U, ∀ rs : List A,
      IsWeaklyRegular (Localization.AtPrime 𝔭.asIdeal) rs →
        IsWeaklyRegular (LocalizedModule 𝔭.asIdeal.primeCompl R) rs := by
  have hJ : J ≤ nilradical A := fun x hx => ⟨n, by simpa [hn] using Ideal.pow_mem_pow hx n⟩
  let h := (isClosedEmbedding_comap_of_surjective _ _
    Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorphOfSurjective
    (comap_quotientMk_bijective_of_le_nilradical hJ).2
  choose W hWo hWd hW using fun k => exists_isOpen_dense_subset_freeLocus_layer (J := J) B R k
  let V : Set (PrimeSpectrum (A ⧸ J)) :=
    ⋂ k ∈ Finset.range n, freeLocus (A ⧸ J) (layer J A k) ∩ W k
  have hVo : ∀ k, IsOpen (freeLocus (A ⧸ J) (layer J A k) ∩ W k) := fun k =>
    isOpen_freeLocus.inter (hWo k)
  have hV : IsOpen V := isOpen_biInter_finset fun k _ => hVo k
  have hVd : Dense V := dense_biInter_range _ hVo (fun k =>
    (dense_of_minimalPrimes_subset fun q hq => mem_freeLocus_of_mem_minimalPrimes q hq)
      |>.inter_of_isOpen_left (hWd k) isOpen_freeLocus) n
  refine ⟨h '' V, h.isOpenMap _ hV, h.surjective.denseRange.dense_image h.continuous hVd, ?_⟩
  rintro _ ⟨q, hq, rfl⟩ rs hrs
  have hq' k (hk : k < n) := Set.mem_iInter₂.1 hq k (Finset.mem_range.2 hk)
  have := free_tensor_layer q (M := A) (by simp [filt, hn]) fun k hk => (hq' k hk).1
  have := free_tensor_layer q (M := R) (by simp [filt, hn]) fun k hk => hW k (hq' k hk).2
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

/-- **Lemme 16, as stated.** The same dense open `U`, for every `A_𝔭`-weakly regular sequence of
`A_𝔭` (each term is a unit times the image of an element of `A`). -/
theorem exists_isOpen_dense_isWeaklyRegular_of_finiteType' {n : ℕ} (hn : J ^ n = ⊥)
    [IsReduced (A ⧸ J)] [Algebra.FiniteType A B] [Module.Finite B R] :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ Dense U ∧
      ∀ 𝔭 ∈ U, ∀ rs : List (Localization.AtPrime 𝔭.asIdeal),
        IsWeaklyRegular (Localization.AtPrime 𝔭.asIdeal) rs →
          IsWeaklyRegular (LocalizedModule 𝔭.asIdeal.primeCompl R) rs := by
  obtain ⟨U, hU, hd, H⟩ := exists_isOpen_dense_isWeaklyRegular_of_finiteType B R hn
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

end Main

end Grothendieck.Folder94

#print axioms Grothendieck.Folder94.exists_isOpen_dense_subset_freeLocus
#print axioms Grothendieck.Folder94.exists_isOpen_dense_subset_freeLocus_layer
#print axioms Grothendieck.Folder94.exists_isOpen_dense_isWeaklyRegular_of_finiteType
#print axioms Grothendieck.Folder94.exists_isOpen_dense_isWeaklyRegular_of_finiteType'
