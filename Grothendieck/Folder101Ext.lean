module

public import Mathlib
public import Grothendieck.Folder101

@[expose] public section


/-!
# Folder 101, page 11: `Ext¹_A(K, A)` as a cokernel, and completeness

Finding `101-sheaf-duality-dim-one`. `Grothendieck/Folder101.lean` proves the page's facts in
the page's own terms: fact b), « every `A`-linear `K → K/A` lifts to `K` » when `A` is complete
(`lift_K`), and its converse (`isAdicComplete_iff_lift`). The page writes fact b) as
`Ext¹_A(K, A) = 0`; that identification was left out, mathlib's categorical `Ext` not being used.
This file supplies it, for mathlib's `Ext` in `ModuleCat A` (`CategoryTheory.Abelian.Ext`, the
morphisms in the derived category):

* `baer_K`: `K` is an injective `A`-module (Baer's criterion, `A` principal), so
  `Ext¹_A(K, K) = 0`;
* `ext_one_eq_zero_iff_lift`: `Ext¹_A(K, A) = 0` if and only if `Hom_A(K, K) → Hom_A(K, K/A)` is
  onto. This is the long exact sequence of `Ext_A(K, -)` for `0 → A → K → K/A → 0`: its segment
  `Hom_A(K, K) → Hom_A(K, K/A) → Ext¹_A(K, A) → Ext¹_A(K, K) = 0` identifies `Ext¹_A(K, A)`
  with the cokernel of the first map;
* `isAdicComplete_iff_ext_one`: for `A` a discrete valuation ring with fraction field `K`, `A`
  is complete if and only if `Ext¹_A(K, A) = 0`, the reading's footnote, now with mathlib's
  `Ext`.

The local cohomology half of the row (`H⁰_x`, `H¹_x` on `Spec A` as derived functors, and the
equivalence between `O_X`-modules and the page's triples) is not formalised here.
-/

namespace Grothendieck.Folder101Ext

open CategoryTheory Abelian IsLocalRing Grothendieck.Folder101

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]

/-- `K` is an injective `A`-module (Baer's criterion; `A` is principal and `K` divisible). -/
theorem baer_K : Module.Baer A K := by
  intro I g
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  rcases eq_or_ne a 0 with rfl | ha
  · refine ⟨0, fun x hx => ?_⟩
    obtain rfl : x = 0 := by simpa using hx
    exact (map_zero g).symm.trans (congrArg g (Subtype.ext rfl))
  have hpa : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ha
  refine ⟨LinearMap.toSpanSingleton A K (g ⟨a, Ideal.mem_span_singleton_self a⟩ /
    algebraMap A K a), fun x hx => ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [LinearMap.toSpanSingleton_apply, mul_smul, Algebra.smul_def a, mul_div_cancel₀ _ hpa,
    ← map_smul]
  rfl

variable (A K) in
/-- The short exact sequence `0 → A → K → K/A → 0` in `ModuleCat A`. -/
noncomputable abbrev ses : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero (Algebra.linearMap A K) (Aₖ A K).mkQ (by
    ext
    simp)

omit [IsDomain A] [IsDiscreteValuationRing A] in
lemma ses_shortExact : (ses A K).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (fun y => by
      change (Aₖ A K).mkQ y = 0 ↔ y ∈ Set.range (Algebra.linearMap A K)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; rfl)
    (IsFractionRing.injective A K) (Submodule.mkQ_surjective _)

/-- **`Ext¹_A(K, A)` is the cokernel of `Hom_A(K, K) → Hom_A(K, K/A)`**, in the form: it vanishes
if and only if that map is onto. -/
theorem ext_one_eq_zero_iff_lift :
    Subsingleton (Ext (ModuleCat.of A K) (ModuleCat.of A A) 1) ↔
      ∀ f : K →ₗ[A] KA A K, ∃ g : K →ₗ[A] K, ∀ x, Submodule.Quotient.mk (g x) = f x := by
  have hS := ses_shortExact (A := A) (K := K)
  have : Injective (ModuleCat.of A K) :=
    Module.injective_object_of_injective_module A K (inj := baer_K.injective)
  constructor
  · intro hE f
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ (ModuleCat.of A K) hS
      (Ext.mk₀ (ModuleCat.ofHom f)) (zero_add 1) (Subsingleton.elim _ _)
    refine ⟨(Ext.homEquiv₀ x₂).hom, fun x => ?_⟩
    rw [← Ext.mk₀_homEquiv₀_apply x₂, Ext.mk₀_comp_mk₀] at hx₂
    have := congrArg (fun φ => (φ : ModuleCat.of A K ⟶ ModuleCat.of A (KA A K)).hom x)
      ((Ext.mk₀_bijective _ _).1 hx₂)
    exact this
  · intro H
    refine ⟨fun e₁ e₂ => ?_⟩
    suffices h0 : ∀ e : Ext (ModuleCat.of A K) (ModuleCat.of A A) 1, e = 0 by
      rw [h0 e₁, h0 e₂]
    intro e
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ (ModuleCat.of A K) hS e
      (Ext.eq_zero_of_injective _) (zero_add 1)
    obtain ⟨g, hg⟩ := H (Ext.homEquiv₀ x₃).hom
    have hx₃ : x₃ = (Ext.mk₀ (ModuleCat.ofHom g)).comp (Ext.mk₀ (ses A K).g) (zero_add 0) := by
      rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_homEquiv₀_apply x₃]
      congr 1
      ext x
      exact (hg x).symm
    rw [hx₃, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- **Completeness is `Ext¹_A(K, A) = 0`.** For a discrete valuation ring `A` with fraction field
`K`, `A` is complete if and only if `Ext¹_A(K, A) = 0` (mathlib's `Ext` in `ModuleCat A`). -/
theorem isAdicComplete_iff_ext_one : IsAdicComplete (maximalIdeal A) A ↔
    Subsingleton (Ext (ModuleCat.of A K) (ModuleCat.of A A) 1) :=
  isAdicComplete_iff_lift.trans ext_one_eq_zero_iff_lift.symm

end Grothendieck.Folder101Ext
