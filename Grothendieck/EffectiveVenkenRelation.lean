module

public import Mathlib
public import Grothendieck.EffectiveVenken
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation

@[expose] public section


/-!
# Venken's relation as an equivalence relation of schemes

`Grothendieck/EffectiveVenken.lean` handles Venken's relation `R ⊂ Spec B × Spec B` through its
ideal `I_V ⊂ B ⊗_K B`: it proves `I_V ⊆ ker(B ⊗ B → B)`, `σ(I_V) ⊆ I_V` for the exchange `σ`,
and `pr₁₃*(I_V) ⊆ pr₁₂*(I_V) + pr₂₃*(I_V)`, and leaves the scheme-theoretic language out.

This file supplies it with the vocabulary of the vendored AxiomMath/Stacks library: a
pre-relation `j : R → U ×_S U` of `S`-schemes (`Stacks.Groupoids.PreRelation`, Stacks tag 022P,
file `StacksFrontier/AlgebraicGeometry/Spaces/EquivalenceRelations.lean`), Mathlib's internal
equivalence relation `CategoryTheory.IsEquivalenceRelation j.target j.source`, its
characterisation as a monic pre-relation inducing an equivalence relation on `T`-valued points
for every `T` (`Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation`,
file `StacksFrontier/AlgebraicGeometry/GroupScheme/Relations/PreRelations.lean`; its tag 022Q,
the induced relation on underlying points, is not needed here), and the groupoid scheme of an equivalence relation
(`AlgebraicGeometry.existsUnique_groupoidScheme_of_isEquivalenceRelation`, tag 0233, file
`StacksFrontier/AlgebraicGeometry/GroupScheme/OverField/GroupoidOfEquivalenceRelation.lean`).

**What is proved.** Let `K` be a commutative ring, `B` a `K`-algebra and `I ⊆ B ⊗_K B` an ideal.
Over `S = Spec K`, with `U = Spec B` and `R = Spec (B ⊗_K B)/I`, let
`relationOfIdeal I : R → U ×_S U` be the pre-relation whose target and source are induced by
`b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`.
* `mono_relationOfIdeal`: it is a monomorphism (a relation);
* `exists_trans`: the algebra of transitivity, two composable `Γ`-points of `(B ⊗ B)/I` with a
  composite, from `pr₁₃*(I) ⊆ pr₁₂*(I) + pr₂₃*(I)`;
* `isEquivalenceRelation_of_ideal` (the translation from equivalence ideals): if
  `I ⊆ ker(B ⊗ B → B)`, `σ(I) ⊆ I` and `pr₁₃*(I) ⊆ pr₁₂*(I) + pr₂₃*(I)`, it is an equivalence
  relation of `S`-schemes. Reflexivity and symmetry are morphisms `U → R`, `R → R` of affine
  schemes; transitivity is checked on `T`-valued points through the `Γ`–`Spec` adjunction,
  where a pair of composable `T`-points of `R` gives a ring map `B ⊗ B ⊗ B → Γ(T)` killing
  `pr₁₂*(I) + pr₂₃*(I)`;
* `existsUnique_groupoidScheme_of_ideal`: it then extends uniquely to a groupoid scheme
  (0233);
* `venken_isEquivalenceRelation`, `venken_existsUnique_groupoidScheme`: Venken's `R`, the
  closed subscheme of `Spec B × Spec B` cut out by `I_V`, is an equivalence relation of schemes
  over `Spec K`, and the scheme of arrows of a unique groupoid scheme. Together with
  `venken_not_effective` (`J_{B^R} ≠ I_V`) this is Venken's statement in the language of
  schemes, the quotient itself being handled through invariants as before.

Not formalised: the contrast with the finite locally free case (Stacks 03BM, whose import
closure is out of reach here), and the identification of effectivity of `R` with the equality
`J_{B^R} = I_V` in scheme-theoretic terms.
-/

namespace Grothendieck.EffectiveVenken.Relation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Groupoids
open scoped TensorProduct

universe u

section Adjunction

variable {X : Scheme.{u}} {A A' : Type u} [CommRing A] [CommRing A']

/-- The ring map `A → Γ(X)` of a morphism `X → Spec A`. -/
noncomputable def ringOf (f : X ⟶ Spec (.of A)) : CommRingCat.of A ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop

theorem ringOf_injective {f g : X ⟶ Spec (.of A)} (h : ringOf f = ringOf g) : f = g :=
  ext_to_Spec h

theorem ringOf_comp_Spec (f : X ⟶ Spec (.of A)) (ψ : CommRingCat.of A' ⟶ CommRingCat.of A) :
    ringOf (f ≫ Spec.map ψ) = ψ ≫ ringOf f := by
  have key : (Scheme.ΓSpecIso _).inv ≫ (Spec.map ψ).appTop = ψ ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Scheme.ΓSpecIso_naturality]
  simp only [ringOf, Scheme.Hom.comp_appTop]
  rw [reassoc_of% key]

/-- The morphism `X → Spec A` of a ring map `A → Γ(X)`. -/
noncomputable def ofRing (φ : CommRingCat.of A ⟶ Γ(X, ⊤)) : X ⟶ Spec (.of A) :=
  X.toSpecΓ ≫ Spec.map φ

theorem ringOf_ofRing (φ : CommRingCat.of A ⟶ Γ(X, ⊤)) : ringOf (ofRing φ) = φ := by
  rw [ofRing, ringOf_comp_Spec, ringOf]
  change φ ≫ (Scheme.ΓSpecIso _).inv ≫ X.toSpecΓ.appTop = φ
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

end Adjunction

variable {K : Type u} [CommRing K] {B : Type u} [CommRing B] [Algebra K B]
  (I : Ideal (B ⊗[K] B))

/-- The base `S = Spec K`. -/
local notation "SpecK" => Spec (CommRingCat.of K)

variable (B) in
/-- `U = Spec B` over `Spec K`. -/
noncomputable abbrev U : Over SpecK :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))

/-- `R = Spec (B ⊗_K B)/I` over `Spec K`. -/
noncomputable abbrev R : Over SpecK :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (B ⊗[K] B ⧸ I))))

/-- `b ↦ b ⊗ 1` into the quotient. -/
noncomputable def inl : B →ₐ[K] B ⊗[K] B ⧸ I :=
  (Ideal.Quotient.mkₐ K I).comp Algebra.TensorProduct.includeLeft

/-- `b ↦ 1 ⊗ b` into the quotient. -/
noncomputable def inr : B →ₐ[K] B ⊗[K] B ⧸ I :=
  (Ideal.Quotient.mkₐ K I).comp Algebra.TensorProduct.includeRight

/-- The morphism of `S`-schemes `Spec C → Spec D` of a `K`-algebra map `D → C`. -/
noncomputable def specHom {C D : Type u} [CommRing C] [CommRing D] [Algebra K C] [Algebra K D]
    (φ : D →ₐ[K] C) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K D))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x)

theorem specHom_left {C D : Type u} [CommRing C] [CommRing D] [Algebra K C] [Algebra K D]
    (φ : D →ₐ[K] C) : (specHom φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

theorem specHom_comp {C D E : Type u} [CommRing C] [CommRing D] [CommRing E] [Algebra K C]
    [Algebra K D] [Algebra K E] (φ : D →ₐ[K] C) (ψ : E →ₐ[K] D) :
    specHom φ ≫ specHom ψ = specHom (φ.comp ψ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, specHom_left, ← Spec.map_comp]
  rfl

theorem specHom_id {C : Type u} [CommRing C] [Algebra K C] :
    specHom (AlgHom.id K C) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [specHom_left]
  exact Spec.map_id _

/-- **The pre-relation of an ideal** `I ⊆ B ⊗_K B`: `Spec (B ⊗ B)/I → Spec B ×_S Spec B`, with
target and source induced by `b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`. -/
noncomputable def relationOfIdeal : PreRelation (R I) (U B) :=
  prod.lift (specHom (inl I)) (specHom (inr I))

theorem target_relationOfIdeal : (relationOfIdeal I).target = specHom (inl I) :=
  prod.lift_fst _ _

theorem source_relationOfIdeal : (relationOfIdeal I).source = specHom (inr I) :=
  prod.lift_snd _ _

/-- Two ring maps out of `(B ⊗ B)/I` agreeing on the `b ⊗ 1` and the `1 ⊗ b` agree. -/
theorem quotient_ringHom_ext {Γ : Type*} [CommRing Γ] {f g : B ⊗[K] B ⧸ I →+* Γ}
    (h₁ : ∀ b, f (inl I b) = g (inl I b)) (h₂ : ∀ b, f (inr I b) = g (inr I b)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul b b' =>
    have : (b ⊗ₜ[K] b' : B ⊗[K] B) = (b ⊗ₜ[K] 1) * (1 ⊗ₜ[K] b') := by simp
    simp only [RingHom.comp_apply, this, map_mul]
    exact congrArg₂ (· * ·) (h₁ b) (h₂ b')
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The ring map `Q → Γ(T)` of a `T`-point of `Spec Q` satisfies `φ ∘ (K → Q) = τ_T`. -/
theorem ringOf_over {C : Type u} [CommRing C] [Algebra K C] {T : Over SpecK}
    (r : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C)))) :
    CommRingCat.ofHom (algebraMap K C) ≫ ringOf r.left = ringOf T.hom := by
  have hw : r.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K C)) = T.hom := Over.w r
  rw [← ringOf_comp_Spec, hw]

/-- The ring map of `f ≫ Spec φ` is `φ` followed by that of `f`. -/
theorem ringOf_left_comp_specHom {C D : Type u} [CommRing C] [CommRing D] [Algebra K C]
    [Algebra K D] (φ : D →ₐ[K] C) {T : Over SpecK}
    (f : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C)))) :
    ringOf (f ≫ specHom φ).left = CommRingCat.ofHom φ.toRingHom ≫ ringOf f.left := by
  rw [Over.comp_left, specHom_left, ringOf_comp_Spec]

/-- **It is a relation**: `j` is a monomorphism. -/
theorem mono_relationOfIdeal : Mono (relationOfIdeal I) := by
  constructor
  intro T f g h
  have h₁ : f ≫ specHom (inl I) = g ≫ specHom (inl I) := by
    have := congrArg (· ≫ prod.fst) h
    simp only [Category.assoc, relationOfIdeal, prod.lift_fst] at this
    exact this
  have h₂ : f ≫ specHom (inr I) = g ≫ specHom (inr I) := by
    have := congrArg (· ≫ prod.snd) h
    simp only [Category.assoc, relationOfIdeal, prod.lift_snd] at this
    exact this
  have e₁ := congrArg (fun k => ringOf k.left) h₁
  have e₂ := congrArg (fun k => ringOf k.left) h₂
  simp only [ringOf_left_comp_specHom] at e₁ e₂
  apply Over.OverMorphism.ext
  apply ringOf_injective
  apply CommRingCat.hom_ext
  exact quotient_ringHom_ext I (fun b => congrArg (fun k => k.hom b) e₁)
    (fun b => congrArg (fun k => k.hom b) e₂)

/-- `b ↦ b ⊗ 1 ⊗ 1`. -/
noncomputable def j₁ : B →ₐ[K] B ⊗[K] (B ⊗[K] B) := Algebra.TensorProduct.includeLeft
/-- `b ↦ 1 ⊗ b ⊗ 1`. -/
noncomputable def j₂ : B →ₐ[K] B ⊗[K] (B ⊗[K] B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft
/-- `b ↦ 1 ⊗ 1 ⊗ b`. -/
noncomputable def j₃ : B →ₐ[K] B ⊗[K] (B ⊗[K] B) :=
  Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight

/-- The algebra of transitivity: two composable points `ψ₁, ψ₂ : (B ⊗ B)/I → Γ` (with
`ψ₁(1 ⊗ b) = ψ₂(b ⊗ 1)`) have a composite `ψ₃`, with `ψ₃(b ⊗ 1) = ψ₁(b ⊗ 1)` and
`ψ₃(1 ⊗ b) = ψ₂(1 ⊗ b)`, as soon as `pr₁₃*(I) ⊆ pr₁₂*(I) + pr₂₃*(I)`. -/
theorem exists_trans {Γ : Type*} [CommRing Γ] [Algebra K Γ]
    (htrans : Ideal.map (Algebra.TensorProduct.productMap (j₁ (K := K) (B := B)) j₃) I ≤
      Ideal.map (Algebra.TensorProduct.productMap (j₁ (K := K) (B := B)) j₂) I ⊔
        Ideal.map (Algebra.TensorProduct.productMap (j₂ (K := K) (B := B)) j₃) I)
    (ψ₁ ψ₂ : B ⊗[K] B ⧸ I →ₐ[K] Γ) (hmid : ∀ b, ψ₁ (inr I b) = ψ₂ (inl I b)) :
    ∃ ψ₃ : B ⊗[K] B ⧸ I →ₐ[K] Γ, (∀ b, ψ₃ (inl I b) = ψ₁ (inl I b)) ∧
      ∀ b, ψ₃ (inr I b) = ψ₂ (inr I b) := by
  let Ψ : B ⊗[K] (B ⊗[K] B) →ₐ[K] Γ :=
    Algebra.TensorProduct.productMap (ψ₁.comp (inl I))
      (Algebra.TensorProduct.productMap (ψ₁.comp (inr I)) (ψ₂.comp (inr I)))
  have h₁₂ : Ψ.comp (Algebra.TensorProduct.productMap j₁ j₂) =
      ψ₁.comp (Ideal.Quotient.mkₐ K I) := by
    apply Algebra.TensorProduct.ext'
    intro b b'
    have : (b ⊗ₜ[K] b' : B ⊗[K] B) = (b ⊗ₜ[K] 1) * (1 ⊗ₜ[K] b') := by simp
    conv_rhs => rw [AlgHom.comp_apply, this, map_mul, map_mul]
    simp [Ψ, j₁, j₂, inl, inr, ← Algebra.TensorProduct.one_def]
  have h₂₃ : Ψ.comp (Algebra.TensorProduct.productMap j₂ j₃) =
      ψ₂.comp (Ideal.Quotient.mkₐ K I) := by
    apply Algebra.TensorProduct.ext'
    intro b b'
    have : (b ⊗ₜ[K] b' : B ⊗[K] B) = (b ⊗ₜ[K] 1) * (1 ⊗ₜ[K] b') := by simp
    have hm := hmid b
    simp only [inl, inr, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mkₐ_eq_mk] at hm
    conv_rhs => rw [AlgHom.comp_apply, this, map_mul, map_mul]
    simp [Ψ, j₂, j₃, inl, inr, hm, ← Algebra.TensorProduct.one_def]
  have hle : Ideal.map (Algebra.TensorProduct.productMap j₁ j₂) I ⊔
      Ideal.map (Algebra.TensorProduct.productMap j₂ j₃) I ≤ RingHom.ker Ψ := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun w hw => ?_)
      (Ideal.map_le_iff_le_comap.2 fun w hw => ?_)
    · change Ψ (Algebra.TensorProduct.productMap j₁ j₂ w) = 0
      rw [← AlgHom.comp_apply, h₁₂]
      simp [Ideal.Quotient.eq_zero_iff_mem.2 hw]
    · change Ψ (Algebra.TensorProduct.productMap j₂ j₃ w) = 0
      rw [← AlgHom.comp_apply, h₂₃]
      simp [Ideal.Quotient.eq_zero_iff_mem.2 hw]
  refine ⟨Ideal.Quotient.liftₐ I (Ψ.comp (Algebra.TensorProduct.productMap j₁ j₃))
    fun w hw => hle (htrans (Ideal.mem_map_of_mem _ hw)), fun b => ?_, fun b => ?_⟩
  · change (Ψ.comp (Algebra.TensorProduct.productMap j₁ j₃)) (b ⊗ₜ[K] 1) = ψ₁ (inl I b)
    simp [Ψ, j₁, j₃, inl, inr, ← Algebra.TensorProduct.one_def]
  · change (Ψ.comp (Algebra.TensorProduct.productMap j₁ j₃)) (1 ⊗ₜ[K] b) = ψ₂ (inr I b)
    simp [Ψ, j₁, j₃, inl, inr, ← Algebra.TensorProduct.one_def]

/-- **The translation from equivalence ideals.** If `I ⊆ ker(B ⊗ B → B)`, `σ(I) ⊆ I` and
`pr₁₃*(I) ⊆ pr₁₂*(I) + pr₂₃*(I)`, the pre-relation `Spec (B ⊗ B)/I → Spec B ×_S Spec B` is an
equivalence relation of `S`-schemes. -/
theorem isEquivalenceRelation_of_ideal
    (hrefl : I ≤ RingHom.ker (Algebra.TensorProduct.lmul' K (S := B)))
    (hsymm : Ideal.map (Algebra.TensorProduct.comm K B B) I ≤ I)
    (htrans : Ideal.map (Algebra.TensorProduct.productMap (j₁ (K := K) (B := B)) j₃) I ≤
      Ideal.map (Algebra.TensorProduct.productMap (j₁ (K := K) (B := B)) j₂) I ⊔
        Ideal.map (Algebra.TensorProduct.productMap (j₂ (K := K) (B := B)) j₃) I) :
    IsEquivalenceRelation (relationOfIdeal I).target (relationOfIdeal I).source := by
  refine (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).2
    ⟨mono_relationOfIdeal I, fun T => ⟨?_, ?_, ?_⟩⟩
  · -- reflexivity: the diagonal `U → R`, from `(B ⊗ B)/I → B`
    intro x
    let μ : B ⊗[K] B ⧸ I →ₐ[K] B := Ideal.Quotient.liftₐ I (Algebra.TensorProduct.lmul' K)
      fun z hz => hrefl hz
    have hμl : μ.comp (inl I) = AlgHom.id K B := by
      ext b
      change Algebra.TensorProduct.lmul' K (b ⊗ₜ[K] (1 : B)) = b
      simp
    have hμr : μ.comp (inr I) = AlgHom.id K B := by
      ext b
      change Algebra.TensorProduct.lmul' K ((1 : B) ⊗ₜ[K] b) = b
      simp
    refine ⟨x ≫ specHom μ, ?_, ?_⟩
    · rw [target_relationOfIdeal, Category.assoc, specHom_comp, hμl, specHom_id,
        Category.comp_id]
    · rw [source_relationOfIdeal, Category.assoc, specHom_comp, hμr, specHom_id,
        Category.comp_id]
  · -- symmetry: the exchange `R → R`, from `σ` on `(B ⊗ B)/I`
    rintro x y ⟨r, hx, hy⟩
    let σ : B ⊗[K] B ⧸ I →ₐ[K] B ⊗[K] B ⧸ I :=
      Ideal.quotientMapₐ I (Algebra.TensorProduct.comm K B B).toAlgHom
        (Ideal.map_le_iff_le_comap.1 hsymm)
    have hσl : σ.comp (inl I) = inr I := by
      ext b; simp [σ, inl, inr]
    have hσr : σ.comp (inr I) = inl I := by
      ext b; simp [σ, inl, inr]
    refine ⟨r ≫ specHom σ, ?_, ?_⟩
    · rw [target_relationOfIdeal, Category.assoc, specHom_comp, hσl, ← source_relationOfIdeal,
        hy]
    · rw [source_relationOfIdeal, Category.assoc, specHom_comp, hσr, ← target_relationOfIdeal,
        hx]
  · -- transitivity, on `T`-points: a ring map `B ⊗ B ⊗ B → Γ(T)`
    rintro x y z ⟨r₁, hx, hy⟩ ⟨r₂, hy', hz⟩
    rw [target_relationOfIdeal] at hx hy'
    rw [source_relationOfIdeal] at hy hz
    let Γ := Γ(T.left, ⊤)
    let _ : Algebra K Γ := (ringOf T.hom).hom.toAlgebra
    have hcomm : ∀ (r : T ⟶ R I) (k : K),
        (ringOf r.left).hom (algebraMap K _ k) = algebraMap K Γ k := fun r k =>
      congrArg (fun φ => φ.hom k) (ringOf_over r)
    let ψ₁ : B ⊗[K] B ⧸ I →ₐ[K] Γ := { (ringOf r₁.left).hom with commutes' := hcomm r₁ }
    let ψ₂ : B ⊗[K] B ⧸ I →ₐ[K] Γ := { (ringOf r₂.left).hom with commutes' := hcomm r₂ }
    -- the middle point: `ψ₁ (1 ⊗ b) = ψ₂ (b ⊗ 1)`
    have hmid : ∀ b, ψ₁ (inr I b) = ψ₂ (inl I b) := by
      have e := congrArg (fun k => ringOf k.left) (hy.trans hy'.symm)
      simp only [ringOf_left_comp_specHom] at e
      exact fun b => congrArg (fun k => k.hom b) e
    obtain ⟨ψ₃, h₃l, h₃r⟩ := exists_trans I htrans ψ₁ ψ₂ hmid
    have hover : ofRing (CommRingCat.ofHom ψ₃.toRingHom) ≫ (R I).hom = T.hom := by
      apply ringOf_injective
      change ringOf (ofRing (CommRingCat.ofHom ψ₃.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K _))) = _
      rw [ringOf_comp_Spec, ringOf_ofRing]
      ext k
      exact ψ₃.commutes k
    let r₃ : T ⟶ R I := Over.homMk (ofRing (CommRingCat.ofHom ψ₃.toRingHom)) hover
    refine ⟨r₃, ?_, ?_⟩
    · rw [target_relationOfIdeal, ← hx]
      apply Over.OverMorphism.ext
      apply ringOf_injective
      rw [ringOf_left_comp_specHom, ringOf_left_comp_specHom]
      change _ ≫ ringOf (ofRing (CommRingCat.ofHom ψ₃.toRingHom)) = _
      rw [ringOf_ofRing]
      ext b
      exact h₃l b
    · rw [source_relationOfIdeal, ← hz]
      apply Over.OverMorphism.ext
      apply ringOf_injective
      rw [ringOf_left_comp_specHom, ringOf_left_comp_specHom]
      change _ ≫ ringOf (ofRing (CommRingCat.ofHom ψ₃.toRingHom)) = _
      rw [ringOf_ofRing]
      ext b
      exact h₃r b

/-- An equivalence ideal defines a groupoid scheme (Stacks 0233): the equivalence relation
`Spec (B ⊗ B)/I → Spec B ×_S Spec B` extends uniquely to a groupoid scheme over `Spec K`. -/
theorem existsUnique_groupoidScheme_of_ideal
    (hrefl : I ≤ RingHom.ker (Algebra.TensorProduct.lmul' K (S := B)))
    (hsymm : Ideal.map (Algebra.TensorProduct.comm K B B) I ≤ I)
    (htrans : Ideal.map (Algebra.TensorProduct.productMap (j₁ (K := K) (B := B)) j₃) I ≤
      Ideal.map (Algebra.TensorProduct.productMap (j₁ (K := K) (B := B)) j₂) I ⊔
        Ideal.map (Algebra.TensorProduct.productMap (j₂ (K := K) (B := B)) j₃) I) :
    ∃! G : GroupoidScheme SpecK, ExtendsRelation (relationOfIdeal I) G := by
  have := isEquivalenceRelation_of_ideal I hrefl hsymm htrans
  exact existsUnique_groupoidScheme_of_isEquivalenceRelation _

variable (K) in
/-- **Venken's relation is an equivalence relation of schemes**: the closed subscheme
`R ⊂ Spec B × Spec B` of ideal `I_V`, over `Spec K`. -/
theorem venken_isEquivalenceRelation :
    IsEquivalenceRelation (relationOfIdeal (venkenRel K)).target
      (relationOfIdeal (venkenRel K)).source :=
  isEquivalenceRelation_of_ideal _ (venkenRel_le_ker_lmul K) (map_comm_venkenRel_le K)
    (map_p₁₃_le K)

variable (K) in
/-- Venken's relation is the scheme of arrows of a unique groupoid scheme over `Spec K`. -/
theorem venken_existsUnique_groupoidScheme :
    ∃! G : GroupoidScheme SpecK, ExtendsRelation (relationOfIdeal (venkenRel K)) G :=
  existsUnique_groupoidScheme_of_ideal _ (venkenRel_le_ker_lmul K) (map_comm_venkenRel_le K)
    (map_p₁₃_le K)

end Grothendieck.EffectiveVenken.Relation
