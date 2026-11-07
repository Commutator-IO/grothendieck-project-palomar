module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/primaryComponent-injective`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/primaryComponent-injective`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean` -/


variable {A M M₁ M₂ : Type*} [CommRing A]
open IsDedekindDomain Submodule Module HeightOneSpectrum Set Function
namespace Ideal
variable (I : Ideal A)
section CommRing
section AddCommMonoid
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]
open Set Function Submodule Module
variable (M)
end AddCommMonoid
section AddCommGroup
variable [AddCommGroup M] [Module A M]
section IsDedekindDomain
variable [IsDedekindDomain A]
open scoped nonZeroDivisors
end IsDedekindDomain
end AddCommGroup
section Injective

universe v

variable {Q : Type v} [AddCommGroup Q] [Module A Q] [IsNoetherianRing A]

private lemma exists_pow_smul_eq_zero_of_primaryComponent_eq_top
    (hQ : primaryComponent Q I = ⊤) (J : Ideal A) (g : J →ₗ[A] Q) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ x : J, a • g x = 0 := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := J)
  have h (x : Q) : ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
    obtain ⟨n, hn⟩ := (primaryComponent_mem Q I x).1 (hQ ▸ mem_top)
    exact ⟨n, fun a ha ↦ (mem_torsionBySet_iff _ _).1 hn ⟨a, ha⟩⟩
  choose e he using fun i ↦ h (g (s i))
  refine ⟨Finset.univ.sup e, fun a ha x ↦ ?_⟩
  have hx : x ∈ Submodule.span A (Set.range s) := hs ▸ mem_top
  induction hx using span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact he i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add, hy, hz, add_zero]
  | smul c y _ hy => rw [map_smul, smul_comm, hy, smul_zero]

theorem baer_of_primaryComponent_eq_top (hQ : primaryComponent Q I = ⊤)
    (h : ∀ (n : ℕ) (N : Submodule A (A ⧸ I ^ n)) (f : N →ₗ[A] Q),
      ∃ g : A ⧸ I ^ n →ₗ[A] Q, ∀ x : N, g x = f x) :
    Module.Baer A Q := by
  intro J g
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_primaryComponent_eq_top I hQ J g
  -- `g` vanishes on `I ^ n • J`.
  have hgIJ (x : A) (hx : x ∈ I ^ n • J) : g ⟨x, smul_le_right hx⟩ = 0 := by
    induction hx using smul_induction_on' with
    | smul a ha y hy => exact (map_smul g a ⟨y, hy⟩).trans (hn a ha _)
    | add x hx y hy hx' hy' =>
      exact (map_add g ⟨x, smul_le_right hx⟩ ⟨y, smul_le_right hy⟩).trans
        (by rw [hx', hy', add_zero])
  -- Artin–Rees: `J ⊓ I ^ (n + k) ≤ I ^ n • J`.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I J
  have hAR (x : A) (hxJ : x ∈ J) (hxm : x ∈ I ^ (n + k)) : x ∈ I ^ n • J := by
    have h1 : x ∈ I ^ (n + k) • (⊤ : Ideal A) ⊓ J := ⟨by simpa using hxm, hxJ⟩
    rw [hk (n + k) (by lia), Nat.add_sub_cancel] at h1
    exact smul_mono le_rfl inf_le_right h1
  -- `g` factors through the image of `J` in `A ⧸ I ^ (n + k)`.
  let φ : J →ₗ[A] A ⧸ I ^ (n + k) := (I ^ (n + k)).mkQ ∘ₗ J.subtype
  have hker : LinearMap.ker φ ≤ LinearMap.ker g := fun x hx ↦ by
    have hxm : (x : A) ∈ I ^ (n + k) := by
      simpa [φ, Ideal.Quotient.eq_zero_iff_mem] using hx
    simpa using hgIJ x (hAR x x.2 hxm)
  obtain ⟨w, hw⟩ := h (n + k) (LinearMap.range φ)
    ((LinearMap.ker φ).liftQ g hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap)
  refine ⟨w ∘ₗ (I ^ (n + k)).mkQ, fun x hx ↦ ?_⟩
  have := hw ⟨φ ⟨x, hx⟩, LinearMap.mem_range_self φ _⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image] at this
  exact this

/-- Over a Noetherian ring, a module `Q` with `Q(I) = Q` is injective as soon as linear maps
into `Q` extend along the inclusions of submodules of `A ⧸ I ^ n`, for all `n`. -/
theorem injective_of_primaryComponent_eq_top (hQ : primaryComponent Q I = ⊤)
    (h : ∀ (n : ℕ) (N : Submodule A (A ⧸ I ^ n)) (f : N →ₗ[A] Q),
      ∃ g : A ⧸ I ^ n →ₗ[A] Q, ∀ x : N, g x = f x) :
    Module.Injective A Q :=
  (baer_of_primaryComponent_eq_top I hQ h).injective

/-- Over a Noetherian ring, the `I`-primary component `Γ_I(Q)` of an injective module `Q` is
injective. -/
@[stacks 08XW "(2)"]
instance primaryComponent.injective [Small.{v} A] [Module.Injective A Q] :
    Module.Injective A (primaryComponent Q I) := by
  refine injective_of_primaryComponent_eq_top I (eq_top_iff.2 fun x _ ↦ ?_) fun n N f ↦ ?_
  · obtain ⟨n, hn⟩ := (primaryComponent_mem Q I x).1 x.2
    refine (primaryComponent_mem _ I x).2 ⟨n, (mem_torsionBySet_iff _ _).2 fun a ↦ ?_⟩
    exact Subtype.ext ((mem_torsionBySet_iff _ _).1 hn a)
  obtain ⟨v, hv⟩ := Module.Injective.extension_property A Q _ _ N.subtype N.injective_subtype
    ((primaryComponent Q I).subtype ∘ₗ f)
  -- The extension lands in `Γ_I(Q)`, because `A ⧸ I ^ n` is killed by `I ^ n`.
  refine ⟨v.codRestrict _ fun y ↦ (primaryComponent_mem Q I _).2 ⟨n,
    (mem_torsionBySet_iff _ _).2 fun a ↦ ?_⟩, fun x ↦ Subtype.ext congr($hv x)⟩
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mul_mem_right b _ a.2), map_zero]

end Injective

end CommRing
end Ideal
