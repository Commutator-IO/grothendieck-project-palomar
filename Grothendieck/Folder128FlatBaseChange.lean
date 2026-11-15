module

public import Mathlib
public import Grothendieck.Folder128
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.EffectiveDescent

@[expose] public section


/-!
# Folder 128, pages 7–9: Cor. 2 and 3 in the affine case, and why « flat » cannot be dropped

Finding `128-nilpotent-conductor-flat-descent`. `Grothendieck/Folder128.lean` proves Cor. 1 and
its example: for `I` a nilpotent ideal of `A` mapped injectively onto an ideal of `S`
(`IsConductorIdeal`), if `S/IS` is faithfully flat over `A/I` then `Spec S → Spec A` is an
effective descent morphism for flat modules
(`Descent.isEffectiveDescentFlat_of_quotient_faithfullyFlat`). That is Cor. 2 for an affine
prescheme `X = Spec A`. This file proves the affine statements only, and adds:

* **Cor. 3, affine case** (`cor3_affine`): under the same hypotheses, for every *flat* ring map
  `A → B`, `Spec (B ⊗_A S) → Spec B` is again an effective descent morphism for flat modules.
  The three hypotheses pass to the base change: `IB` is nilpotent (`isNilpotent_map`); `IB` is
  mapped injectively onto an ideal of `B ⊗_A S` (`isConductorIdeal_baseChange`, the only step
  where `B` must be flat: `I ⊗_A B → B ⊗_A S` is injective because `I → S` is); and
  `(B ⊗_A S)/IB(B ⊗_A S) ≅ B/IB ⊗_{A/I} S/IS` is faithfully flat over `B/IB`
  (`faithfullyFlat_quotient_baseChange`, for any `B`).
* **The restriction to flat modules is needed** (`example_isEffectiveDescentFlat`,
  `example_not_isEffectiveDescentMorphismForModules`). For a field `k`, `S = k[ε] × k[ε]`
  (`ε² = 0`) and `A = {(a + bε, a + cε)}` with `I = {(bε, cε)}`, the hypotheses of Cor. 2
  hold, so `Spec S → Spec A` is an effective descent morphism for flat modules; but it is not
  one for all modules in the sense of AxiomMath/Stacks: base extension from `A`-modules to
  descent data is not an equivalence (`ModuleCat.IsEffectiveDescentMorphismForModules`, Stacks
  tag 08WY). The proof uses Stacks tag 08XA, vendored under `lean/Stacks/`
  (`ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective`: effective descent
  for all modules is universal injectivity). Here `A → S` is not universally injective: for
  `Q = A/(u − v)`, `u = (ε, 0)`, `v = (0, ε)`, the element `u ⊗ 1` is nonzero in `A ⊗_A Q`, but
  in `S ⊗_A Q` it is `(1, 0) ⊗ ū = (1, 0) ⊗ v̄ = 0` (`not_injective_rTensor`). The same `A`, `S`
  and `Q` are the reading's counterexample to Cor. 3 for a non-flat `Y = Spec A/(u − v)`.

Not formalised: Cor. 2 and 3 for non-affine preschemes (gluing the affine statements along an
open cover, which needs quasi-coherent descent data on schemes), which stay out of reach here.
-/

namespace Grothendieck.Folder128FlatBaseChange

open TensorProduct Grothendieck.Folder128.Descent

universe u

section BaseChange

variable {A S B : Type u} [CommRing A] [CommRing S] [Algebra A S] [CommRing B] [Algebra A B]

/-- A nilpotent ideal stays nilpotent after extension. -/
lemma isNilpotent_map {I : Ideal A} (hI : IsNilpotent I) :
    IsNilpotent (I.map (algebraMap A B)) := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩

/-- For `B` flat over `A`, an ideal `I` of `A` mapped injectively onto an ideal of `S` gives the
ideal `IB` of `B` mapped injectively onto an ideal of `B ⊗_A S`. -/
theorem isConductorIdeal_baseChange [Module.Flat A B] {I : Ideal A}
    (h : IsConductorIdeal S I) :
    IsConductorIdeal (B ⊗[A] S) (I.map (algebraMap A B)) where
  inj x hx h0 := by
    have hx' : x ∈ (I • ⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hx
    rw [← range_smulMap] at hx'
    obtain ⟨t, rfl⟩ := hx'
    let ν : I ⊗[A] B →ₗ[A] B ⊗[A] S := (TensorProduct.comm A S B).toLinearMap ∘ₗ
      (Algebra.linearMap A S ∘ₗ I.subtype).rTensor B
    have hν : Function.Injective ν := (TensorProduct.comm A S B).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _
        (fun x y hxy => Subtype.ext (sub_eq_zero.1 (h.inj _ (I.sub_mem x.2 y.2)
          (by rw [map_sub, sub_eq_zero]; exact hxy)))))
    have he : ∀ t, algebraMap B (B ⊗[A] S) (smulMap I B t) = ν t := fun t => by
      induction t using TensorProduct.inductionOn with
      | tmul r b =>
        simp only [ν, smulMap_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearMap.rTensor_tmul, Submodule.coe_subtype, Algebra.linearMap_apply,
          TensorProduct.comm_tmul, Algebra.TensorProduct.algebraMap_apply]
        rw [Algebra.algebraMap_eq_smul_one (A := S), ← smul_tmul, Algebra.algebraMap_self,
          RingHom.id_apply]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [he] at h0
    rw [hν (h0.trans (map_zero ν).symm), map_zero]
  ideal x hx c := by
    -- the set of `z` of the form `y ⊗ 1` with `y ∈ IB`
    let P : B ⊗[A] S → Prop := fun z => ∃ y ∈ I.map (algebraMap A B), z = algebraMap B _ y
    have hP0 : P 0 := ⟨0, Submodule.zero_mem _, (map_zero _).symm⟩
    have hPadd : ∀ z w, P z → P w → P (z + w) := by
      rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      exact ⟨y + y', Submodule.add_mem _ hy hy', (map_add _ _ _).symm⟩
    suffices H : ∀ c : B ⊗[A] S, P (c * algebraMap B _ x) by
      obtain ⟨y, hy, e⟩ := H c; exact ⟨y, hy, e⟩
    intro c
    induction c using TensorProduct.inductionOn with
    | add c c' hc hc' => rw [add_mul]; exact hPadd _ _ hc hc'
    | tmul b s =>
      induction hx using Submodule.span_induction with
      | zero => simpa using hP0
      | add x y _ _ hx hy => rw [map_add, mul_add]; exact hPadd _ _ hx hy
      | smul r x _ hx =>
        obtain ⟨y, hy, e⟩ := hx
        refine ⟨r * y, Ideal.mul_mem_left _ r hy, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, mul_left_comm, e]
      | mem z hz =>
        obtain ⟨a, ha, rfl⟩ := hz
        obtain ⟨a', ha', e⟩ := h.ideal a ha s
        refine ⟨algebraMap A B a' * b, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha'), ?_⟩
        have e' : a • s = a' • (1 : S) := by
          rw [Algebra.smul_def, mul_comm, e, Algebra.algebraMap_eq_smul_one]
        change (b ⊗ₜ[A] s) * ((algebraMap A B a) ⊗ₜ[A] (1 : S)) =
          (algebraMap A B a' * b) ⊗ₜ[A] (1 : S)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm b, ← Algebra.smul_def,
          ← Algebra.smul_def, smul_tmul, e', ← smul_tmul]

/-- `(B ⊗_A S)/IB(B ⊗_A S)` is faithfully flat over `B/IB` when `S/IS` is faithfully flat over
`A/I`, for any `B`: it is `B/IB ⊗_{A/I} S/IS`. -/
theorem faithfullyFlat_quotient_baseChange {I : Ideal A}
    [Module.FaithfullyFlat (A ⧸ I) (S ⧸ I.map (algebraMap A S))] :
    Module.FaithfullyFlat (B ⧸ I.map (algebraMap A B))
      ((B ⊗[A] S) ⧸ (I.map (algebraMap A B)).map (algebraMap B (B ⊗[A] S))) := by
  let A₀ := A ⧸ I
  let B₀ := B ⧸ I.map (algebraMap A B)
  have h1 : Module.FaithfullyFlat A₀ (A₀ ⊗[A] S) :=
    Module.FaithfullyFlat.of_linearEquiv _ _
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv.symm
  have h2 : Module.FaithfullyFlat B₀ (B₀ ⊗[A] S) :=
    Module.FaithfullyFlat.of_linearEquiv _ _
      (AlgebraTensorModule.cancelBaseChange A A₀ B₀ B₀ S).symm
  let e := Algebra.TensorProduct.quotientTensorEquiv (R := A) B S B (I.map (algebraMap A B))
  let e' : (B₀ ⊗[A] S) ≃ₗ[B₀]
      ((B ⊗[A] S) ⧸ (I.map (algebraMap A B)).map (algebraMap B (B ⊗[A] S))) :=
    { e.toLinearEquiv with
      map_smul' := fun c x => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        change e _ = _ • e x
        rw [RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul]
        exact map_smul e b x }
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e'.symm

/-- **Folder 128, Cor. 3, affine case** (Grothendieck, page 9). Let `I` be a nilpotent ideal of
`A` mapped isomorphically onto an ideal of `S`, with `S/IS` faithfully flat over `A/I`. For every
flat `A`-algebra `B`, `Spec (B ⊗_A S) → Spec B` is an effective descent morphism for flat
modules. (`B = A` is Cor. 2 for `X = Spec A`.) -/
theorem cor3_affine [Module.Flat A B] {I : Ideal A} (h : IsConductorIdeal S I)
    (hI : IsNilpotent I) [Module.FaithfullyFlat (A ⧸ I) (S ⧸ I.map (algebraMap A S))] :
    IsEffectiveDescentFlat B (B ⊗[A] S) :=
  haveI := faithfullyFlat_quotient_baseChange (B := B) (S := S) (I := I)
  isEffectiveDescentFlat_of_quotient_faithfullyFlat (isConductorIdeal_baseChange h)
    (isNilpotent_map hI)

end BaseChange

section Example

open TrivSqZeroExt

variable (k : Type u) [Field k]

/-- `S = k[ε] × k[ε]`, `ε² = 0` (`k[ε] = TrivSqZeroExt k k`), kept as its own type so that
instance problems over it do not unfold the product. -/
def ExS : Type u := TrivSqZeroExt k k × TrivSqZeroExt k k

noncomputable instance : CommRing (ExS k) :=
  inferInstanceAs (CommRing (TrivSqZeroExt k k × TrivSqZeroExt k k))

noncomputable instance : Algebra k (ExS k) :=
  inferInstanceAs (Algebra k (TrivSqZeroExt k k × TrivSqZeroExt k k))

variable {k}

/-- The two factors `S → k[ε]`. -/
noncomputable def pr₁ : ExS k →+* TrivSqZeroExt k k := RingHom.fst _ _

/-- The two factors `S → k[ε]`. -/
noncomputable def pr₂ : ExS k →+* TrivSqZeroExt k k := RingHom.snd _ _

/-- The element `(a, b)` of `S`. -/
def mkS (a b : TrivSqZeroExt k k) : ExS k := (a, b)

@[simp] lemma pr₁_mkS (a b : TrivSqZeroExt k k) : pr₁ (mkS a b) = a := rfl

@[simp] lemma pr₂_mkS (a b : TrivSqZeroExt k k) : pr₂ (mkS a b) = b := rfl

@[simp] lemma pr₁_algebraMap (c : k) : pr₁ (algebraMap k (ExS k) c) = algebraMap k _ c := rfl

@[simp] lemma pr₂_algebraMap (c : k) : pr₂ (algebraMap k (ExS k) c) = algebraMap k _ c := rfl

lemma ExS.ext {x y : ExS k} (h₁ : pr₁ x = pr₁ y) (h₂ : pr₂ x = pr₂ y) : x = y :=
  Prod.ext h₁ h₂

variable (k)

/-- `A = {(a + bε, a + cε)} ⊂ k[ε] × k[ε]`. -/
noncomputable def exA : Subalgebra k (ExS k) where
  carrier := {x | (pr₁ x).fst = (pr₂ x).fst}
  mul_mem' {x y} (hx : (pr₁ x).fst = (pr₂ x).fst) (hy : (pr₁ y).fst = (pr₂ y).fst) := by
    change (pr₁ (x * y)).fst = (pr₂ (x * y)).fst
    simp [hx, hy]
  add_mem' {x y} (hx : (pr₁ x).fst = (pr₂ x).fst) (hy : (pr₁ y).fst = (pr₂ y).fst) := by
    change (pr₁ (x + y)).fst = (pr₂ (x + y)).fst
    simp [hx, hy]
  algebraMap_mem' c := by
    change (pr₁ (algebraMap k (ExS k) c)).fst = (pr₂ (algebraMap k (ExS k) c)).fst
    simp

/-- The ring `A`, as a type with its commutative ring structure. -/
def ExA : Type u := exA k

noncomputable instance : CommRing (ExA k) := inferInstanceAs (CommRing (exA k))

noncomputable instance : Algebra k (ExA k) := inferInstanceAs (Algebra k (exA k))

noncomputable instance : Algebra (ExA k) (ExS k) := inferInstanceAs (Algebra (exA k) (ExS k))

variable {k}

/-- The inclusion `A → S`. -/
noncomputable abbrev ι (x : ExA k) : ExS k := algebraMap (ExA k) (ExS k) x

lemma ι_fst (x : ExA k) : (pr₁ (ι x)).fst = (pr₂ (ι x)).fst := (show exA k from x).2

lemma ι_injective : Function.Injective (ι : ExA k → ExS k) := Subtype.val_injective

/-- An element of `S` with equal constant terms, as an element of `A`. -/
noncomputable def mkA (y : ExS k) (hy : (pr₁ y).fst = (pr₂ y).fst) : ExA k :=
  (⟨y, hy⟩ : exA k)

@[simp] lemma ι_mkA (y : ExS k) (hy : (pr₁ y).fst = (pr₂ y).fst) : ι (mkA y hy) = y := rfl

variable (k)

/-- `a + bε ↦ a` on `A`. -/
noncomputable def exAug : ExA k →+* k :=
  ((fstHom k k k).toRingHom.comp pr₁).comp (algebraMap (ExA k) (ExS k))

/-- `I = {(bε, cε)}`, the kernel of the augmentation. -/
noncomputable def exI : Ideal (ExA k) := RingHom.ker (exAug k)

lemma exAug_surjective : Function.Surjective (exAug k) := fun c =>
  ⟨algebraMap k (ExA k) c,
    show (pr₁ (algebraMap k (ExS k) c)).fst = c by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩

variable {k} in
lemma mem_exI {x : ExA k} : x ∈ exI k ↔ (pr₁ (ι x)).fst = 0 := Iff.rfl

lemma isConductorIdeal_exI : IsConductorIdeal (ExS k) (exI k) where
  inj x _ hx := ι_injective (hx.trans (map_zero _).symm)
  ideal x hx b := by
    have h1 : (pr₁ (ι x)).fst = 0 := hx
    have h2 : (pr₂ (ι x)).fst = 0 := ι_fst x ▸ h1
    refine ⟨mkA (b * ι x) (by simp [h1, h2]), ?_, rfl⟩
    rw [mem_exI, ι_mkA]
    simp [h1]

lemma isNilpotent_exI : IsNilpotent (exI k) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  have hx1 : (pr₁ (ι x)).fst = 0 := hx
  have hx2 : (pr₂ (ι x)).fst = 0 := ι_fst x ▸ hx1
  have hy1 : (pr₁ (ι y)).fst = 0 := hy
  have hy2 : (pr₂ (ι y)).fst = 0 := ι_fst y ▸ hy1
  rw [Ideal.mem_bot]
  apply ι_injective
  simp only [ι, map_mul, map_zero]
  apply ExS.ext <;> ext <;> simp [hx1, hx2, hy1, hy2]

lemma map_exI_ne_top : (exI k).map (algebraMap (ExA k) (ExS k)) ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one, (isConductorIdeal_exI k).mem_map]
  rintro ⟨x, hx, e⟩
  have h1 : (pr₁ (ι x)).fst = 0 := hx
  rw [ι, e, map_one] at h1
  exact one_ne_zero h1

lemma faithfullyFlat_exI :
    Module.FaithfullyFlat (ExA k ⧸ exI k)
      (ExS k ⧸ (exI k).map (algebraMap (ExA k) (ExS k))) := by
  have : (exI k).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (exAug_surjective k)
  let := Ideal.Quotient.field (exI k)
  have : Nontrivial (ExS k ⧸ (exI k).map (algebraMap (ExA k) (ExS k))) :=
    Ideal.Quotient.nontrivial_iff.2 (map_exI_ne_top k)
  infer_instance

/-- In the example, `Spec S → Spec A` is an effective descent morphism for flat modules
(Cor. 2 applies). -/
theorem example_isEffectiveDescentFlat : IsEffectiveDescentFlat (ExA k) (ExS k) :=
  haveI := faithfullyFlat_exI k
  isEffectiveDescentFlat_of_quotient_faithfullyFlat (isConductorIdeal_exI k) (isNilpotent_exI k)

/-- `u = (ε, 0)`. -/
noncomputable def exU : ExA k := mkA (mkS (inr 1) 0) (by simp)

/-- `v = (0, ε)`. -/
noncomputable def exV : ExA k := mkA (mkS 0 (inr 1)) (by simp)

lemma exU_not_mem : exU k ∉ Ideal.span {exU k - exV k} := by
  rw [Ideal.mem_span_singleton']
  rintro ⟨a, ha⟩
  have hfst := ι_fst a
  have e1 := congrArg (fun z : ExA k => (pr₁ (ι z)).snd) ha
  have e2 := congrArg (fun z : ExA k => (pr₂ (ι z)).snd) ha
  simp only [ι, map_mul, map_sub, exU, exV] at e1 e2
  simp at e1 e2
  rw [hfst, e2] at e1
  exact zero_ne_one e1

/-- The test module `Q = A/(u − v)`. -/
abbrev ExQ : Type u := ExA k ⧸ Ideal.span {exU k - exV k}

/-- `A → S` is not universally injective: `u ⊗ 1 ≠ 0` in `A ⊗_A Q`, but its image in
`S ⊗_A Q` is `0`. -/
theorem not_injective_rTensor :
    ¬ Function.Injective ((Algebra.linearMap (ExA k) (ExS k)).rTensor (ExQ k)) := by
  intro hinj
  have hsm : ∀ a : ExA k, a • (Ideal.Quotient.mk _ 1 : ExQ k) = Ideal.Quotient.mk _ a :=
    fun a => by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]
  have hne : exU k ⊗ₜ[ExA k] (Ideal.Quotient.mk _ 1 : ExQ k) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid (ExA k) (ExQ k)) h0
    rw [TensorProduct.lid_tmul, map_zero, hsm] at this
    exact exU_not_mem k (Ideal.Quotient.eq_zero_iff_mem.1 this)
  have hu : algebraMap (ExA k) (ExS k) (exU k) = exU k • mkS 1 0 := by
    rw [Algebra.smul_def]
    apply ExS.ext <;> ext <;> simp [exU]
  have hv : exV k • (mkS 1 0 : ExS k) = 0 := by
    rw [Algebra.smul_def]
    apply ExS.ext <;> ext <;> simp [exV]
  have huv : exU k • (Ideal.Quotient.mk _ 1 : ExQ k) = exV k • Ideal.Quotient.mk _ 1 := by
    rw [hsm, hsm]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self _)
  apply hne
  apply hinj
  rw [map_zero, LinearMap.rTensor_tmul, Algebra.linearMap_apply, hu, smul_tmul, huv,
    ← smul_tmul, hv, zero_tmul]

/-- **Flatness cannot be dropped.** In the example, `Spec S → Spec A` is not an effective descent
morphism for all modules (base extension to descent data is not an equivalence, Stacks tag
08WY): by Stacks tag 08XA it would be universally injective. -/
theorem example_not_isEffectiveDescentMorphismForModules.{w} :
    ¬ ModuleCat.IsEffectiveDescentMorphismForModules.{u, u, w} (ExA k) (ExS k) := by
  rw [ModuleCat.isEffectiveDescentMorphismForModules_iff_universallyInjective]
  exact fun h => not_injective_rTensor k (h (ExQ k))

end Example

end Grothendieck.Folder128FlatBaseChange
