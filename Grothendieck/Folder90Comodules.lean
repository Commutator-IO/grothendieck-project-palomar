module

public import Mathlib

@[expose] public section


/-!
# Folder 90, pages 7–9 and 13–15: the smallest subcomodule, over `X = S = Spec A`

The modernised reading `transcripts/90/90.modern.tex` states on page 13, for an affine group
`G` over a base `S` whose algebra `B` is a filtered union of submodules `Bᵢ` with
1) `B/Bᵢ` flat, 2) `Δ Bᵢ ⊆ Bᵢ ⊗ Bᵢ`, 3) `Bᵢ` locally free of finite type, and a
quasi-coherent `G`-module `E` on an `S`-scheme `X` with trivial action:

> 1) tout sous-module quasi-cohérent `F` de `E` est contenu dans un plus petit sous-module
> quasi-cohérent `F'` stable par `G` ; sa formation commute à tout changement de base plat ;
> si `F` est de type fini, `F'` aussi ;
> 2) si `X` est quasi-compact et quasi-séparé, `E` est réunion filtrante de sous-modules
> quasi-cohérents de type fini stables par `G`.

The page gives no proof; the reading supplies `F' = Σᵢ Uᵢ · (F ∩ Eᵢ)`, `Uᵢ = Bᵢ*`, from the
`Uᵢ`-module description of pages 7–9. This is finding `90-equivariant-resolution-general-base`;
here is its ring case, `X = S = Spec A`. Mathlib has coalgebras but no comodules, so the file
defines them (`Comodule`: a coaction `δ : E → B ⊗ E`, counital and coassociative) and
subcomodules (`IsSubcomodule B N`: `δ N ⊆ B ⊗ N`, i.e. inside the image of `B ⊗ N → B ⊗ E`).
The hypothesis is `Exhaustion A B ι`: `B = ⋃ Bᵢ` directed, `Bᵢ` finite projective,
`B ⧸ Bᵢ` flat, `Δ Bᵢ` in the image of `Bᵢ ⊗ Bᵢ`. Proved here, for any commutative ring `A`:

* `Exhaustion.closure`: `F′`, the span of the `(u ⊗ id) y` with `y ∈ Bᵢ ⊗ E` lifting `δ f`,
  `f ∈ F`, `u ∈ Uᵢ` — the reading's formula;
* `Exhaustion.isLeast_closure`: `F′` is the smallest subcomodule containing `F` (statement 1);
* `Exhaustion.closure_fg`: `F′` is of finite type when `F` is; then `F′ = Uᵢ · F` for one `i`;
* `Exhaustion.exists_fg_isSubcomodule`, `IsSubcomodule.sup`: every element of `E` lies in a
  subcomodule of finite type, and these are stable under sums, so `E` is their filtered union
  (statement 2 for `X = S` affine);
* `Exhaustion.map_closure`: `φ(F′) = (φ F)′` for every morphism of comodules `φ`;
* `comoduleBaseChange`: `A' ⊗ E` is a comodule over the `A'`-coalgebra `A' ⊗ B` (Mathlib's
  base change of coalgebras), for every `A`-algebra `A'`;
* `isLeast_closure_baseChange`: the image of `A' ⊗ F′` in `A' ⊗ E` is the smallest
  subcomodule containing the image of `A' ⊗ F`, for **every** `A'`;
  `baseChange_closure_injective`: when `A'` is flat, that image is `A' ⊗ F′` itself, which is
  the page's « sa formation commute à tout changement de base plat ».

The steps: the page's flatness step `(Bᵢ ⊗ E) ∩ (B ⊗ N) = Bᵢ ⊗ N`
(`mem_range_lTensor_of_rTensor_mem`, from `B ⧸ Bᵢ` flat by Mathlib's
`lTensor_injective_of_exact_of_flat`) gives minimality; coassociativity and a dual basis of
`Bᵢ` give `δ(u · y) = Σₖ bₖ ⊗ (u * bₖ*) · y` (`coact_coeff`), whence stability and finiteness.

**What the formalisation finds.** Statement 1) holds over any commutative ring as the reading
completes it, with base change in a stronger form: the compatibility holds for every `A'` once
stated with images, flatness of `A'` serving only to identify the image with `A' ⊗ F′`. The
flatness of `B ⧸ Bᵢ` enters only through the injectivity of `Bᵢ ⊗ M → B ⊗ M` (for
minimality, and in `coact_coeff` with `M = B ⊗ E`); `Δᵢ : Bᵢ → Bᵢ ⊗ Bᵢ` is lifted by
projectivity. Not formalised: quasi-coherent sheaves on a scheme `X`
(the page's general case, its gluing and the quasi-compact quasi-separated hypothesis of 2)),
statements 3) and 4), the equivalence `Cᵢ(G)_f ≃ Uᵢ-modules` of page 7, and the action of `G` on
`X` of pages 17–23.
-/

open TensorProduct LinearMap

namespace Grothendieck.Folder90Comodules

variable {A : Type*} [CommRing A]

/-- A comodule over an `A`-coalgebra `B`: an `A`-module `E` with a coaction `δ : E → B ⊗ E`,
counital and coassociative (page 7 of folder 90; « `A`-`G`-module »). -/
class Comodule (A : Type*) (B E : Type*) [CommRing A] [AddCommGroup B] [Module A B]
    [Coalgebra A B] [AddCommGroup E] [Module A E] where
  coact : E →ₗ[A] B ⊗[A] E
  counit_coact : (TensorProduct.lid A E).toLinearMap ∘ₗ
    (Coalgebra.counit (R := A) (A := B)).rTensor E ∘ₗ coact = LinearMap.id
  coassoc : (TensorProduct.assoc A B B E).toLinearMap ∘ₗ
    (Coalgebra.comul (R := A) (A := B)).rTensor E ∘ₗ coact = coact.lTensor B ∘ₗ coact

/-- **Flatness of the quotient.** If `B ⧸ N` is flat, `N ⊗ M → B ⊗ M` is injective. -/
theorem rTensor_subtype_injective {B : Type*} [AddCommGroup B] [Module A B] (N : Submodule A B)
    [Module.Flat A (B ⧸ N)] (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (N.subtype.rTensor M) := by
  have h := LinearMap.lTensor_injective_of_exact_of_flat N.mkQ N.mkQ_surjective N.subtype
    N.injective_subtype (LinearMap.exact_subtype_mkQ N) M
  have : N.subtype.rTensor M = (TensorProduct.comm A M B).toLinearMap ∘ₗ N.subtype.lTensor M ∘ₗ
      (TensorProduct.comm A N M).toLinearMap := by
    ext; simp
  rw [this]
  simpa using h


variable {B E : Type*} [AddCommGroup B] [Module A B] [Coalgebra A B] [AddCommGroup E] [Module A E]

/-- A submodule `N ⊆ E` is a **subcomodule** (« stable par `G` ») if `δ N ⊆ B ⊗ N`. -/
def IsSubcomodule (B : Type*) [AddCommGroup B] [Module A B] [Coalgebra A B]
    [Comodule A B E] (N : Submodule A E) : Prop :=
  ∀ e ∈ N, Comodule.coact (A := A) (B := B) e ∈ LinearMap.range (N.subtype.lTensor B)

omit [Coalgebra A B] in
theorem sum_tmul_mem_range {κ : Type*} (s : Finset κ) (N : Submodule A E) (b : κ → B)
    (e : κ → E) (he : ∀ k ∈ s, e k ∈ N) :
    ∑ k ∈ s, b k ⊗ₜ[A] e k ∈ LinearMap.range (N.subtype.lTensor B) :=
  Submodule.sum_mem _ fun k hk => ⟨b k ⊗ₜ ⟨e k, he k hk⟩, rfl⟩

variable [Comodule A B E] in
theorem isSubcomodule_span {s : Set E}
    (h : ∀ e ∈ s, Comodule.coact (A := A) (B := B) e ∈
      LinearMap.range ((Submodule.span A s).subtype.lTensor B)) :
    IsSubcomodule B (Submodule.span A s) := by
  intro e he
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

variable [Comodule A B E] in
/-- The sum of two subcomodules is a subcomodule. -/
theorem IsSubcomodule.sup {N₁ N₂ : Submodule A E} (h₁ : IsSubcomodule B N₁)
    (h₂ : IsSubcomodule B N₂) : IsSubcomodule B (N₁ ⊔ N₂) := by
  have mono : ∀ {N N' : Submodule A E}, N ≤ N' → LinearMap.range (N.subtype.lTensor B) ≤
      LinearMap.range (N'.subtype.lTensor B) := fun {N N'} h => by
    rw [← Submodule.subtype_comp_inclusion _ _ h, LinearMap.lTensor_comp]
    exact LinearMap.range_comp_le_range _ _
  intro e he
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 he
  rw [map_add]
  exact Submodule.add_mem _ (mono le_sup_left (h₁ x hx)) (mono le_sup_right (h₂ y hy))

variable [Comodule A B E] in
/-- The image of a subcomodule by a morphism of comodules is a subcomodule. -/
theorem IsSubcomodule.map {E₂ : Type*} [AddCommGroup E₂] [Module A E₂] [Comodule A B E₂]
    {φ : E →ₗ[A] E₂} (hφ : Comodule.coact (A := A) (B := B) ∘ₗ φ =
      φ.lTensor B ∘ₗ Comodule.coact (A := A) (B := B))
    {N : Submodule A E} (hN : IsSubcomodule B N) : IsSubcomodule B (N.map φ) := by
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨x, hx⟩ := hN e he
  refine ⟨(φ.submoduleMap N).lTensor B x, ?_⟩
  have h := LinearMap.congr_fun hφ e
  simp only [LinearMap.comp_apply] at h
  rw [h, ← hx, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    ← LinearMap.lTensor_comp]
  rfl

/-- The hypothesis of pages 7 and 13: `B` is the filtered union of submodules `Bᵢ`, finite
projective, with `B ⧸ Bᵢ` flat and `Δ Bᵢ ⊆ Bᵢ ⊗ Bᵢ`. -/
structure Exhaustion (A : Type*) (B : Type*) [CommRing A] [AddCommGroup B] [Module A B]
    [Coalgebra A B] (ι : Type*) where
  Bi : ι → Submodule A B
  nonempty : Nonempty ι
  directed : Directed (· ≤ ·) Bi
  exhaustive : ∀ b : B, ∃ i, b ∈ Bi i
  finite : ∀ i, Module.Finite A (Bi i)
  projective : ∀ i, Module.Projective A (Bi i)
  flat : ∀ i, Module.Flat A (B ⧸ Bi i)
  comul_mem : ∀ i, ∀ b ∈ Bi i, Coalgebra.comul (R := A) b ∈
    LinearMap.range (TensorProduct.map (Bi i).subtype (Bi i).subtype)

namespace Exhaustion

variable {ι : Type*} (H : Exhaustion A B ι)

/-- The comultiplication restricted to `Bᵢ`, `Δᵢ : Bᵢ → Bᵢ ⊗ Bᵢ`. -/
theorem exists_comulI (i : ι) : ∃ d : H.Bi i →ₗ[A] H.Bi i ⊗[A] H.Bi i,
    TensorProduct.map (H.Bi i).subtype (H.Bi i).subtype ∘ₗ d =
      Coalgebra.comul (R := A) ∘ₗ (H.Bi i).subtype := by
  have := H.projective i
  obtain ⟨d, hd⟩ := Module.projective_lifting_property
    (TensorProduct.map (H.Bi i).subtype (H.Bi i).subtype).rangeRestrict
    ((Coalgebra.comul (R := A) ∘ₗ (H.Bi i).subtype).codRestrict _
      fun b => H.comul_mem i b b.2) (LinearMap.surjective_rangeRestrict _)
  exact ⟨d, LinearMap.ext fun b => congrArg Subtype.val (LinearMap.congr_fun hd b)⟩

/-- `Δᵢ`. -/
noncomputable def comulI (i : ι) : H.Bi i →ₗ[A] H.Bi i ⊗[A] H.Bi i :=
  (H.exists_comulI i).choose

theorem map_comulI (i : ι) : TensorProduct.map (H.Bi i).subtype (H.Bi i).subtype ∘ₗ H.comulI i =
    Coalgebra.comul (R := A) ∘ₗ (H.Bi i).subtype :=
  (H.exists_comulI i).choose_spec

/-- A finite dual basis of `Bᵢ` (finite projective). -/
theorem exists_dualBasis (i : ι) : ∃ (n : ℕ) (b : Fin n → H.Bi i)
    (bs : Fin n → Module.Dual A (H.Bi i)), ∀ x, ∑ k, bs k x • b k = x := by
  have := H.projective i
  have := H.finite i
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (H.Bi i)
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun k => f (Pi.single k 1), fun k => LinearMap.proj k ∘ₗ g, fun x => ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := A) x, ← hg]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, ← map_smul, ← map_sum]
  congr 1
  ext m
  simp [Finset.sum_apply, Pi.single_apply]

theorem rTensor_injective (i : ι) (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective ((H.Bi i).subtype.rTensor M) :=
  haveI := H.flat i
  rTensor_subtype_injective _ M

/-- The size of the chosen dual basis of `Bᵢ`. -/
noncomputable def dim (i : ι) : ℕ := (H.exists_dualBasis i).choose

/-- The chosen dual basis `(bₖ)` of `Bᵢ`. -/
noncomputable def bas (i : ι) : Fin (H.dim i) → H.Bi i :=
  (H.exists_dualBasis i).choose_spec.choose

/-- The chosen dual basis `(bₖ*)` of `Bᵢ`. -/
noncomputable def dual (i : ι) : Fin (H.dim i) → Module.Dual A (H.Bi i) :=
  (H.exists_dualBasis i).choose_spec.choose_spec.choose

theorem sum_dual_smul_bas (i : ι) (x : H.Bi i) : ∑ k, H.dual i k x • H.bas i k = x :=
  (H.exists_dualBasis i).choose_spec.choose_spec.choose_spec x

/-- Every linear form on `Bᵢ` is `u = Σₖ u(bₖ) bₖ*`. -/
theorem dual_eq_sum (i : ι) (u : Module.Dual A (H.Bi i)) :
    u = ∑ k, u (H.bas i k) • H.dual i k := by
  ext x
  conv_lhs => rw [← H.sum_dual_smul_bas i x]
  simp [map_sum, mul_comm]

/-- The convolution `u * v = (u ⊗ v) ∘ Δᵢ` in the dual algebra `Uᵢ = Bᵢ*`. -/
noncomputable def conv (i : ι) (u v : Module.Dual A (H.Bi i)) : Module.Dual A (H.Bi i) :=
  (TensorProduct.lid A A).toLinearMap ∘ₗ TensorProduct.map u v ∘ₗ H.comulI i

/-- The restriction of the counit to `Bᵢ`, the unit of `Uᵢ`. -/
noncomputable def counitI (i : ι) : Module.Dual A (H.Bi i) :=
  Coalgebra.counit (R := A) (A := B) ∘ₗ (H.Bi i).subtype

variable (E) in
/-- The action of `u ∈ Uᵢ` on an element `y ∈ Bᵢ ⊗ E`: `(u ⊗ id) y ∈ E`. When `y` is the
coaction of `e`, this is `u · e` of page 7. -/
noncomputable def coeff (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) : E :=
  TensorProduct.lid A E (u.rTensor E y)

theorem coeff_eq_sum (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) :
    H.coeff E i y u = ∑ k, u (H.bas i k) • H.coeff E i y (H.dual i k) := by
  have h : u.rTensor E = ∑ k, u (H.bas i k) • (H.dual i k).rTensor E := by
    calc u.rTensor E = LinearMap.rTensorHom E u := rfl
      _ = LinearMap.rTensorHom E (∑ k, u (H.bas i k) • H.dual i k) := by
        rw [← H.dual_eq_sum i u]
      _ = _ := by simp only [map_sum, map_smul]; rfl
  simp [coeff, h, LinearMap.sum_apply, map_sum]

theorem range_mono {i j : ι} (hij : H.Bi i ≤ H.Bi j) :
    LinearMap.range ((H.Bi i).subtype.rTensor E) ≤
      LinearMap.range ((H.Bi j).subtype.rTensor E) := by
  rw [← Submodule.subtype_comp_inclusion _ _ hij, LinearMap.rTensor_comp]
  exact LinearMap.range_comp_le_range _ _

/-- Every element of `B ⊗ E` lies in some `Bᵢ ⊗ E`. -/
theorem exists_mem_range (x : B ⊗[A] E) :
    ∃ i, x ∈ LinearMap.range ((H.Bi i).subtype.rTensor E) := by
  induction x with
  | tmul b e =>
    obtain ⟨i, hi⟩ := H.exhaustive b
    exact ⟨i, ⟨⟨b, hi⟩ ⊗ₜ e, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    obtain ⟨k, hik, hjk⟩ := H.directed i j
    exact ⟨k, Submodule.add_mem _ (H.range_mono hik hi) (H.range_mono hjk hj)⟩

/-- Finitely many elements of `B ⊗ E` lie in a common `Bᵢ ⊗ E`. -/
theorem exists_mem_range_finset (s : Finset (B ⊗[A] E)) :
    ∃ i, ∀ x ∈ s, x ∈ LinearMap.range ((H.Bi i).subtype.rTensor E) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨H.nonempty.some, by simp⟩
  | insert x s _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := H.exists_mem_range x
    obtain ⟨k, hik, hjk⟩ := H.directed i j
    refine ⟨k, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact H.range_mono hjk hj
    · exact H.range_mono hik (hi y hy)

section Comodule

variable [Comodule A B E]

/-- The key computation: if `y ∈ Bᵢ ⊗ E` lifts `δ f`, then `δ(u · y) = Σₖ bₖ ⊗ (u * bₖ*) · y`. -/
theorem coact_coeff {i : ι} {y : H.Bi i ⊗[A] E} {f : E}
    (hy : (H.Bi i).subtype.rTensor E y = Comodule.coact (A := A) (B := B) f)
    (u : Module.Dual A (H.Bi i)) :
    Comodule.coact (A := A) (B := B) (H.coeff E i y u) =
      ∑ k, ((H.bas i k : B) ⊗ₜ[A] H.coeff E i y (H.conv i u (H.dual i k))) := by
  set ι' := (H.Bi i).subtype
  set δ := Comodule.coact (A := A) (B := B) (E := E)
  set w := TensorProduct.assoc A _ _ E ((H.comulI i).rTensor E y)
  -- step 1: `(id ⊗ δ) y = (id ⊗ ι ⊗ id) w`
  have h1 : δ.lTensor (H.Bi i) y = (ι'.rTensor E).lTensor (H.Bi i) w := by
    apply H.rTensor_injective i (B ⊗[A] E)
    have e1 : ι'.rTensor (B ⊗[A] E) ∘ₗ δ.lTensor (H.Bi i) = δ.lTensor B ∘ₗ ι'.rTensor E := by
      ext; simp
    have e2 : (TensorProduct.assoc A B B E).toLinearMap ∘ₗ
        (TensorProduct.map ι' ι').rTensor E =
        ι'.rTensor (B ⊗[A] E) ∘ₗ (ι'.rTensor E).lTensor (H.Bi i) ∘ₗ
          (TensorProduct.assoc A _ _ E).toLinearMap := by
      ext; simp
    have e3 := LinearMap.congr_fun (Comodule.coassoc (A := A) (B := B) (E := E)) f
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at e3
    calc ι'.rTensor (B ⊗[A] E) (δ.lTensor (H.Bi i) y)
        = δ.lTensor B (ι'.rTensor E y) := LinearMap.congr_fun e1 y
      _ = TensorProduct.assoc A B B E
            ((Coalgebra.comul (R := A) ∘ₗ ι').rTensor E y) := by
          rw [hy, ← e3, LinearMap.rTensor_comp, LinearMap.comp_apply, hy]
      _ = TensorProduct.assoc A B B E
            ((TensorProduct.map ι' ι').rTensor E ((H.comulI i).rTensor E y)) := by
          rw [← H.map_comulI i, LinearMap.rTensor_comp, LinearMap.comp_apply]
      _ = _ := LinearMap.congr_fun e2 _
  -- step 2: `δ(u · y) = (ι ⊗ id) z`
  have e4 : δ ∘ₗ (TensorProduct.lid A E).toLinearMap ∘ₗ u.rTensor E =
      (TensorProduct.lid A (B ⊗[A] E)).toLinearMap ∘ₗ u.rTensor (B ⊗[A] E) ∘ₗ
        δ.lTensor (H.Bi i) := by
    ext; simp
  have e5 : (TensorProduct.lid A (B ⊗[A] E)).toLinearMap ∘ₗ u.rTensor (B ⊗[A] E) ∘ₗ
      (ι'.rTensor E).lTensor (H.Bi i) =
      ι'.rTensor E ∘ₗ (TensorProduct.lid A (H.Bi i ⊗[A] E)).toLinearMap ∘ₗ
        u.rTensor (H.Bi i ⊗[A] E) := by
    ext; simp
  set z := TensorProduct.lid A (H.Bi i ⊗[A] E) (u.rTensor (H.Bi i ⊗[A] E) w)
  have h2 : δ (H.coeff E i y u) = ι'.rTensor E z := by
    calc δ (H.coeff E i y u) = _ := LinearMap.congr_fun e4 y
      _ = _ := by simp only [LinearMap.coe_comp, Function.comp_apply, h1]
      _ = _ := LinearMap.congr_fun e5 w
  -- step 3: the dual basis
  have e6 : ∀ x : H.Bi i ⊗[A] E, ∑ k, H.bas i k ⊗ₜ[A]
      TensorProduct.lid A E ((H.dual i k).rTensor E x) = x := by
    intro x
    induction x with
    | tmul b e =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.tmul_smul]
      simp_rw [TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, H.sum_dual_smul_bas]
    | add x x' hx hx' =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hx']
  -- step 4: identification of the coefficients
  have e7 : ∀ k, (TensorProduct.lid A E).toLinearMap ∘ₗ (H.dual i k).rTensor E ∘ₗ
      (TensorProduct.lid A (H.Bi i ⊗[A] E)).toLinearMap ∘ₗ u.rTensor (H.Bi i ⊗[A] E) ∘ₗ
      (TensorProduct.assoc A _ _ E).toLinearMap =
      (TensorProduct.lid A E).toLinearMap ∘ₗ
        ((TensorProduct.lid A A).toLinearMap ∘ₗ TensorProduct.map u (H.dual i k)).rTensor E := by
    intro k
    ext a b e
    simp [mul_smul]
  rw [h2, ← e6 z, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.rTensor_tmul]
  congr 1
  have := LinearMap.congr_fun (e7 k) ((H.comulI i).rTensor E y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
  rw [coeff, conv, ← LinearMap.comp_assoc, LinearMap.rTensor_comp, LinearMap.comp_apply]
  exact this

omit [Comodule A B E] in
/-- **The page's flatness step**: `(Bᵢ ⊗ E) ∩ (B ⊗ N) = Bᵢ ⊗ N` inside `B ⊗ E`. -/
theorem mem_range_lTensor_of_rTensor_mem (i : ι) (N : Submodule A E) {y : H.Bi i ⊗[A] E}
    (h : (H.Bi i).subtype.rTensor E y ∈ LinearMap.range (N.subtype.lTensor B)) :
    y ∈ LinearMap.range (N.subtype.lTensor (H.Bi i)) := by
  obtain ⟨x, hx⟩ := h
  have hex := lTensor_exact (H.Bi i) (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
  obtain ⟨w, hw⟩ := (hex y).1 (by
    apply H.rTensor_injective i (E ⧸ N)
    rw [map_zero]
    have e1 : (H.Bi i).subtype.rTensor (E ⧸ N) ∘ₗ N.mkQ.lTensor (H.Bi i) =
        N.mkQ.lTensor B ∘ₗ (H.Bi i).subtype.rTensor E := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    have e2 : N.mkQ.lTensor B ∘ₗ N.subtype.lTensor B = 0 := by
      rw [← LinearMap.lTensor_comp, show N.mkQ ∘ₗ N.subtype = 0 from LinearMap.ext fun x => by simp,
        LinearMap.lTensor_zero]
    rw [← LinearMap.comp_apply, e1, LinearMap.comp_apply, ← hx, ← LinearMap.comp_apply, e2,
      LinearMap.zero_apply])
  exact ⟨w, hw⟩

/-- The counit acts as the identity: if `y` lifts `δ f`, then `ε · y = f`. -/
theorem coeff_counitI {i : ι} {y : H.Bi i ⊗[A] E} {f : E}
    (hy : (H.Bi i).subtype.rTensor E y = Comodule.coact (A := A) (B := B) f) :
    H.coeff E i y (H.counitI i) = f := by
  rw [coeff, counitI, LinearMap.rTensor_comp, LinearMap.comp_apply, hy]
  exact LinearMap.congr_fun Comodule.counit_coact f

/-- The generators `u · (F ∩ Eᵢ)` of `F′`: the `(u ⊗ id) y` with `y ∈ Bᵢ ⊗ E` lifting `δ f`,
`f ∈ F`, `u ∈ Uᵢ`. -/
def lifts (F : Submodule A E) : Set E :=
  {e | ∃ (i : ι) (y : H.Bi i ⊗[A] E) (u : Module.Dual A (H.Bi i)) (f : E), f ∈ F ∧
    (H.Bi i).subtype.rTensor E y = Comodule.coact (A := A) (B := B) f ∧ H.coeff E i y u = e}

/-- **`F′ = Σᵢ Uᵢ · (F ∩ Eᵢ)`** (the formula of the reading, pages 13–15). -/
def closure (F : Submodule A E) : Submodule A E :=
  Submodule.span A (H.lifts F)

/-- `F ⊆ F′`. -/
theorem le_closure (F : Submodule A E) : F ≤ H.closure F := fun f hf => by
  obtain ⟨i, y, hy⟩ := H.exists_mem_range (Comodule.coact (A := A) (B := B) f)
  exact Submodule.subset_span ⟨i, y, H.counitI i, f, hf, hy, H.coeff_counitI hy⟩

/-- `F′` is a subcomodule. -/
theorem isSubcomodule_closure (F : Submodule A E) : IsSubcomodule B (H.closure F) := by
  refine isSubcomodule_span fun e he => ?_
  obtain ⟨i, y, u, f, hf, hy, rfl⟩ := he
  rw [H.coact_coeff hy u]
  exact sum_tmul_mem_range _ _ _ _ fun k _ =>
    Submodule.subset_span ⟨i, y, _, f, hf, hy, rfl⟩

/-- `F′` is contained in every subcomodule containing `F`. -/
theorem closure_le {F N : Submodule A E} (hN : IsSubcomodule B N) (hF : F ≤ N) :
    H.closure F ≤ N := by
  refine Submodule.span_le.2 fun e he => ?_
  obtain ⟨i, y, u, f, hf, hy, rfl⟩ := he
  have h := hN f (hF hf)
  rw [← hy] at h
  obtain ⟨w, rfl⟩ := H.mem_range_lTensor_of_rTensor_mem i N h
  have e1 : (TensorProduct.lid A E).toLinearMap ∘ₗ u.rTensor E ∘ₗ N.subtype.lTensor (H.Bi i) =
      N.subtype ∘ₗ (TensorProduct.lid A N).toLinearMap ∘ₗ u.rTensor N := by
    ext; simp
  have := LinearMap.congr_fun e1 w
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
  rw [coeff, this]
  exact Submodule.coe_mem _

/-- **Statement 1) of page 13, for `X = S = Spec A`**: every submodule `F` of a comodule lies
in a smallest subcomodule, `F′`. -/
theorem isLeast_closure (F : Submodule A E) :
    IsLeast {N : Submodule A E | IsSubcomodule B N ∧ F ≤ N} (H.closure F) :=
  ⟨⟨H.isSubcomodule_closure F, H.le_closure F⟩, fun _ hN => H.closure_le hN.1 hN.2⟩

/-- **`F′` is of finite type when `F` is**: for `F = A·f₁ + ⋯ + A·fₘ` with every `δ fⱼ` in a
common `Bᵢ ⊗ E`, `F′ = Uᵢ · F` is spanned by the `bₖ* · fⱼ`. -/
theorem closure_fg {F : Submodule A E} (hF : F.FG) : (H.closure F).FG := by
  classical
  obtain ⟨S, rfl⟩ := hF
  obtain ⟨i, hi⟩ := H.exists_mem_range_finset (S.image (Comodule.coact (A := A) (B := B)))
  choose y hy using fun f (hf : f ∈ S) => hi _ (Finset.mem_image_of_mem _ hf)
  let gen : S × Fin (H.dim i) → E := fun p => H.coeff E i (y p.1 p.1.2) (H.dual i p.2)
  let G := Submodule.span A (Set.range gen)
  have memG : ∀ (f : E) (hf : f ∈ S) u, H.coeff E i (y f hf) u ∈ G := fun f hf u => by
    rw [H.coeff_eq_sum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨f, hf⟩, k), rfl⟩)
  have hG : IsSubcomodule B G := by
    refine isSubcomodule_span ?_
    rintro _ ⟨⟨⟨f, hf⟩, k⟩, rfl⟩
    rw [H.coact_coeff (hy f hf)]
    exact sum_tmul_mem_range _ _ _ _ fun m _ => memG f hf _
  have hSG : Submodule.span A (S : Set E) ≤ G := Submodule.span_le.2 fun f hf => by
    rw [← H.coeff_counitI (hy f hf)]
    exact memG f hf _
  have hGc : G ≤ H.closure (Submodule.span A (S : Set E)) := Submodule.span_le.2 <| by
    rintro _ ⟨⟨⟨f, hf⟩, k⟩, rfl⟩
    exact Submodule.subset_span ⟨i, y f hf, H.dual i k, f, Submodule.subset_span hf, hy f hf, rfl⟩
  rw [le_antisymm (H.closure_le hG hSG) hGc]
  exact ⟨(Finset.univ.image gen), by simp [G]⟩

include H in
/-- **Statement 2) of page 13, for `X = S = Spec A`**: every element lies in a subcomodule of
finite type, and the subcomodules of finite type form a directed family; `E` is their filtered
union. -/
theorem exists_fg_isSubcomodule (e : E) :
    ∃ N : Submodule A E, N.FG ∧ IsSubcomodule B N ∧ e ∈ N :=
  ⟨H.closure (A ∙ e), H.closure_fg (Submodule.fg_span_singleton e),
    H.isSubcomodule_closure _, H.le_closure _ (Submodule.mem_span_singleton_self e)⟩

theorem fg_sup_isSubcomodule {N₁ N₂ : Submodule A E} (h₁ : N₁.FG ∧ IsSubcomodule B N₁)
    (h₂ : N₂.FG ∧ IsSubcomodule B N₂) : (N₁ ⊔ N₂).FG ∧ IsSubcomodule B (N₁ ⊔ N₂) :=
  ⟨h₁.1.sup h₂.1, h₁.2.sup h₂.2⟩

/-- **The formation of `F′` commutes with morphisms of comodules**: `φ(F′) = (φ F)′`. -/
theorem map_closure {E₂ : Type*} [AddCommGroup E₂] [Module A E₂] [Comodule A B E₂]
    (φ : E →ₗ[A] E₂) (hφ : Comodule.coact (A := A) (B := B) ∘ₗ φ =
      φ.lTensor B ∘ₗ Comodule.coact (A := A) (B := B)) (F : Submodule A E) :
    (H.closure F).map φ = H.closure (F.map φ) := by
  refine le_antisymm ?_ (H.closure_le ((H.isSubcomodule_closure F).map hφ)
    (Submodule.map_mono (H.le_closure F)))
  rw [closure, Submodule.map_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨i, y, u, f, hf, hy, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨i, φ.lTensor _ y, u, φ f, ⟨f, hf, rfl⟩, ?_, ?_⟩
  · rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hy, ← LinearMap.comp_apply, ← hφ, LinearMap.comp_apply]
  · have e1 : (TensorProduct.lid A E₂).toLinearMap ∘ₗ u.rTensor E₂ ∘ₗ φ.lTensor (H.Bi i) =
        φ ∘ₗ (TensorProduct.lid A E).toLinearMap ∘ₗ u.rTensor E := by
      ext; simp
    exact LinearMap.congr_fun e1 y

end Comodule

end Exhaustion

/-! ### Base change -/

section BaseChange

variable [Comodule A B E] (A' : Type*) [CommRing A'] [Algebra A A']

/-- `A' ⊗ E` as an `A`-comodule over `B`: `a ⊗ e ↦ Σ bₖ ⊗ (a ⊗ eₖ)`. -/
noncomputable instance comoduleRestrict : Comodule A B (A' ⊗[A] E) where
  coact := (TensorProduct.leftComm A A' B E).toLinearMap ∘ₗ
    (Comodule.coact (A := A) (B := B) (E := E)).lTensor A'
  counit_coact := by
    ext a e
    have g : ∀ x : B ⊗[A] E, TensorProduct.lid A (A' ⊗[A] E)
        ((Coalgebra.counit (R := A) (A := B)).rTensor _ (TensorProduct.leftComm A A' B E
          (a ⊗ₜ x))) = a ⊗ₜ TensorProduct.lid A E
            ((Coalgebra.counit (R := A) (A := B)).rTensor E x) := by
      intro x
      induction x with
      | tmul b e => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have := g (Comodule.coact (A := A) (B := B) e)
    simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearMap.lTensor_tmul, LinearMap.id_coe, id_eq,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars] at this ⊢
    rw [this]
    congr 1
    exact LinearMap.congr_fun (Comodule.counit_coact (A := A) (B := B) (E := E)) e
  coassoc := by
    ext a e
    have g1 : ∀ x : B ⊗[A] E, TensorProduct.assoc A B B (A' ⊗[A] E)
        ((Coalgebra.comul (R := A) (A := B)).rTensor _ (TensorProduct.leftComm A A' B E
          (a ⊗ₜ x))) = ((TensorProduct.leftComm A A' B E).toLinearMap.lTensor B)
            (TensorProduct.leftComm A A' B (B ⊗[A] E) (a ⊗ₜ TensorProduct.assoc A B B E
              ((Coalgebra.comul (R := A) (A := B)).rTensor E x))) := by
      intro x
      induction x with
      | tmul b e =>
        simp only [TensorProduct.leftComm_tmul, LinearMap.rTensor_tmul]
        induction Coalgebra.comul (R := A) b with
        | tmul c d => simp
        | add x y hx hy => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have g2 : ∀ x : B ⊗[A] E,
        (((TensorProduct.leftComm A A' B E).toLinearMap ∘ₗ
          (Comodule.coact (A := A) (B := B) (E := E)).lTensor A').lTensor B)
          (TensorProduct.leftComm A A' B E (a ⊗ₜ x)) =
        ((TensorProduct.leftComm A A' B E).toLinearMap.lTensor B)
            (TensorProduct.leftComm A A' B (B ⊗[A] E) (a ⊗ₜ
              (Comodule.coact (A := A) (B := B) (E := E)).lTensor B x)) := by
      intro x
      induction x with
      | tmul b e => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have h3 := LinearMap.congr_fun (Comodule.coassoc (A := A) (B := B) (E := E)) e
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h3
    simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearMap.lTensor_tmul, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars] at g1 g2 ⊢
    rw [g1, g2, h3]

/-- **The base change** `A' ⊗ E`, a comodule over the `A'`-coalgebra `A' ⊗ B`. -/
noncomputable instance comoduleBaseChange : Comodule A' (A' ⊗[A] B) (A' ⊗[A] E) where
  coact := (AlgebraTensorModule.distribBaseChange A A' B E).toLinearMap ∘ₗ
    (Comodule.coact (A := A) (B := B) (E := E)).baseChange A'
  counit_coact := by
    ext e
    have g : ∀ x : B ⊗[A] E, TensorProduct.lid A' (A' ⊗[A] E)
        ((Coalgebra.counit (R := A') (A := A' ⊗[A] B)).rTensor _
          (AlgebraTensorModule.distribBaseChange A A' B E (1 ⊗ₜ x))) =
        (1 : A') ⊗ₜ TensorProduct.lid A E ((Coalgebra.counit (R := A) (A := B)).rTensor E x) := by
      intro x
      induction x with
      | tmul b e => simp [TensorProduct.smul_tmul']
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have h := LinearMap.congr_fun (Comodule.counit_coact (A := A) (B := B) (E := E)) e
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
    simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.baseChange_tmul, LinearMap.id_coe, id_eq]
    rw [g, h, LinearMap.id_apply]
  coassoc := by
    ext e
    let Ψ : B ⊗[A] (B ⊗[A] E) →ₗ[A] (A' ⊗[A] B) ⊗[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] E)) :=
      ((AlgebraTensorModule.distribBaseChange A A' B E).toLinearMap.lTensor (A' ⊗[A] B) ∘ₗ
        (AlgebraTensorModule.distribBaseChange A A' B (B ⊗[A] E)).toLinearMap).restrictScalars A ∘ₗ
        TensorProduct.mk A A' _ 1
    have g1 : ∀ x : B ⊗[A] E, TensorProduct.assoc A' (A' ⊗[A] B) (A' ⊗[A] B) (A' ⊗[A] E)
        ((Coalgebra.comul (R := A') (A := A' ⊗[A] B)).rTensor _
          (AlgebraTensorModule.distribBaseChange A A' B E (1 ⊗ₜ x))) =
        Ψ (TensorProduct.assoc A B B E ((Coalgebra.comul (R := A) (A := B)).rTensor E x)) := by
      intro x
      induction x with
      | tmul b e =>
        simp only [AlgebraTensorModule.distribBaseChange_tmul, LinearMap.rTensor_tmul,
          TensorProduct.comul_tmul]
        induction Coalgebra.comul (R := A) b with
        | tmul c d => simp [Ψ]
        | add x y hx hy =>
          simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have g2 : ∀ x : B ⊗[A] E,
        (((AlgebraTensorModule.distribBaseChange A A' B E).toLinearMap ∘ₗ
          (Comodule.coact (A := A) (B := B) (E := E)).baseChange A').lTensor (A' ⊗[A] B))
          (AlgebraTensorModule.distribBaseChange A A' B E (1 ⊗ₜ x)) =
        Ψ ((Comodule.coact (A := A) (B := B) (E := E)).lTensor B x) := by
      intro x
      induction x with
      | tmul b e => simp [Ψ]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    have h3 := LinearMap.congr_fun (Comodule.coassoc (A := A) (B := B) (E := E)) e
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h3
    simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, TensorProduct.curry_apply, LinearMap.coe_restrictScalars,
      LinearMap.baseChange_tmul] at g2 ⊢
    rw [g1, g2, h3]

/-- `e ↦ 1 ⊗ e` is a morphism of `A`-comodules `E → A' ⊗ E`. -/
theorem coact_comp_mk :
    Comodule.coact (A := A) (B := B) (E := A' ⊗[A] E) ∘ₗ TensorProduct.mk A A' E 1 =
      (TensorProduct.mk A A' E 1).lTensor B ∘ₗ Comodule.coact (A := A) (B := B) (E := E) := by
  ext e
  change TensorProduct.leftComm A A' B E (1 ⊗ₜ _) =
    (TensorProduct.mk A A' E 1).lTensor B (Comodule.coact (A := A) (B := B) e)
  generalize Comodule.coact (A := A) (B := B) e = x
  induction x with
  | tmul b e => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- `(A' ⊗ B) ⊗_{A'} E' → B ⊗_A E'`, `(a ⊗ b) ⊗ e ↦ b ⊗ a e`. -/
noncomputable def theta : (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] E) →ₗ[A] B ⊗[A] (A' ⊗[A] E) :=
  (TensorProduct.comm A (A' ⊗[A] E) B).toLinearMap ∘ₗ
    ((AlgebraTensorModule.cancelBaseChange A A' A' (A' ⊗[A] E) B).toLinearMap ∘ₗ
      (TensorProduct.comm A' (A' ⊗[A] B) (A' ⊗[A] E)).toLinearMap).restrictScalars A

theorem theta_coact (e : A' ⊗[A] E) :
    theta (B := B) A' (Comodule.coact (A := A') (B := A' ⊗[A] B) e) =
      Comodule.coact (A := A) (B := B) e := by
  induction e with
  | tmul a e =>
    change theta A' (AlgebraTensorModule.distribBaseChange A A' B E (a ⊗ₜ _)) =
      TensorProduct.leftComm A A' B E (a ⊗ₜ _)
    induction Comodule.coact (A := A) (B := B) e with
    | tmul b e => simp [theta, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- An `A'`-subcomodule of `A' ⊗ E` (over `A' ⊗ B`) is an `A`-subcomodule (over `B`). -/
theorem IsSubcomodule.restrictScalars {N : Submodule A' (A' ⊗[A] E)}
    (hN : IsSubcomodule (A' ⊗[A] B) N) : IsSubcomodule B (N.restrictScalars A) := by
  intro e he
  obtain ⟨x, hx⟩ := hN e he
  rw [← theta_coact, ← hx]
  clear hx
  induction x with
  | tmul c n =>
    induction c with
    | tmul a b =>
      refine ⟨b ⊗ₜ ⟨a • (n : A' ⊗[A] E), N.smul_mem a n.2⟩, ?_⟩
      simp [theta]
    | add c c' hc hc' =>
      rw [TensorProduct.add_tmul, map_add, map_add]
      exact Submodule.add_mem _ hc hc'
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

variable {ι : Type*} (H : Exhaustion A B ι)

/-- **Base change.** For any `A`-algebra `A'`, the image of `A' ⊗ F′` in `A' ⊗ E` is the
smallest subcomodule of `A' ⊗ E` (over the `A'`-coalgebra `A' ⊗ B`) containing the image of
`A' ⊗ F`: the formation of `F′` commutes with base change. -/
theorem isLeast_closure_baseChange (F : Submodule A E) :
    IsLeast {N : Submodule A' (A' ⊗[A] E) | IsSubcomodule (A' ⊗[A] B) N ∧
        LinearMap.range (F.subtype.baseChange A') ≤ N}
      (LinearMap.range ((H.closure F).subtype.baseChange A')) := by
  have hspan : ∀ N : Submodule A E, LinearMap.range (N.subtype.baseChange A') =
      Submodule.span A' (N.map (TensorProduct.mk A A' E 1)) := fun N => by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, rfl⟩
      induction x with
      | tmul a n =>
        rw [LinearMap.baseChange_tmul, ← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨n, n.2, rfl⟩)
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · rintro _ ⟨n, hn, rfl⟩
      exact ⟨1 ⊗ₜ ⟨n, hn⟩, rfl⟩
  rw [hspan, hspan]
  refine ⟨⟨isSubcomodule_span ?_, Submodule.span_mono
    (Submodule.map_mono (H.le_closure F))⟩, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx⟩ := H.isSubcomodule_closure F g hg
    change AlgebraTensorModule.distribBaseChange A A' B E (1 ⊗ₜ _) ∈ _
    rw [← hx]
    clear hx
    induction x with
    | tmul b n =>
      exact ⟨(1 ⊗ₜ b) ⊗ₜ ⟨1 ⊗ₜ (n : E), Submodule.subset_span ⟨n, n.2, rfl⟩⟩, rfl⟩
    | add x y hx hy =>
      rw [map_add, TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
  · rintro N ⟨hN, hFN⟩
    have hA := hN.restrictScalars A'
    have h1 : F.map (TensorProduct.mk A A' E 1) ≤ N.restrictScalars A :=
      fun x hx => hFN (Submodule.subset_span hx)
    have h2 := H.closure_le hA h1
    rw [← H.map_closure _ (coact_comp_mk A') F] at h2
    exact Submodule.span_le.2 h2

/-- For `A'` flat over `A`, `A' ⊗ F′ → A' ⊗ E` is injective, so the image above is
`A' ⊗ F′` itself. -/
theorem baseChange_closure_injective [Module.Flat A A'] (F : Submodule A E) :
    Function.Injective ((H.closure F).subtype.baseChange A') := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)

end BaseChange

end Grothendieck.Folder90Comodules
