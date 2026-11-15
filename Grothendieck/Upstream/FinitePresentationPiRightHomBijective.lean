module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/finitePresentation-piRightHom-bijective`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4,
branch `mycaule/finitePresentation-piRightHom-bijective`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/Algebra/Exact/Basic.lean` -/

section
variable {R M M' N N' P P' : Type*}
namespace Function
variable (f : M → N) (g : N → P) (g' : P → P')
variable {f g}
namespace MulExact
@[to_additive /-- A product of exact pairs is exact. -/]
lemma piMap {ι : Type*} {α β γ : ι → Type*} [∀ i, One (γ i)] {f : ∀ i, α i → β i}
    {g : ∀ i, β i → γ i} (h : ∀ i, MulExact (f i) (g i)) : MulExact (Pi.map f) (Pi.map g) := by
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · choose x hx using fun i ↦ (h i (y i)).1 (congrFun hy i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    exact funext fun i ↦ (h i _).2 ⟨x i, rfl⟩

@[to_additive /-- A product of two exact pairs is exact. -/]
lemma prodMap {M₁ N₁ P₁ M₂ N₂ P₂ : Type*} [One P₁] [One P₂] {f₁ : M₁ → N₁} {g₁ : N₁ → P₁}
    {f₂ : M₂ → N₂} {g₂ : N₂ → P₂} (h₁ : MulExact f₁ g₁) (h₂ : MulExact f₂ g₂) :
    MulExact (Prod.map f₁ f₂) (Prod.map g₁ g₂) := by
  rintro ⟨y₁, y₂⟩
  simp [Set.range_prodMap, h₁ y₁, h₂ y₂]

end MulExact
end Function
section MonoidHom
variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}
namespace MonoidHom
open Function
end MonoidHom
namespace Function.MulExact
open MonoidHom
section
variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommMonoid X₁] [CommMonoid X₂] [CommMonoid X₃]
  [CommMonoid Y₁] [CommMonoid Y₂] [CommMonoid Y₃]
  (e₁ : X₁ ≃* Y₁) (e₂ : X₂ ≃* Y₂) (e₃ : X₃ ≃* Y₃)
  {f₁₂ : X₁ →* X₂} {f₂₃ : X₂ →* X₃} {g₁₂ : Y₁ →* Y₂} {g₂₃ : Y₂ →* Y₃}
end
end Function.MulExact
end MonoidHom
section LinearMap
open Function
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
namespace LinearMap
section Ring
variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
end Ring
end LinearMap
namespace Function
open LinearMap
namespace Exact
variable
    {f₁₂ : M →ₗ[R] N} {f₂₃ : N →ₗ[R] P} {g₁₂ : M' →ₗ[R] N'}
    {g₂₃ : N' →ₗ[R] P'} {e₁ : M ≃ₗ[R] M'} {e₂ : N ≃ₗ[R] N'} {e₃ : P ≃ₗ[R] P'}
end Exact
end Function
end LinearMap
namespace Function
section split
variable [Semiring R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}
open LinearMap
end split
section Prod
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
end Prod
end Function
section Ring
open LinearMap Submodule
variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
namespace Function
end Function
namespace LinearMap
end LinearMap
end Ring
end

/-! ## From `Mathlib/Algebra/Module/FinitePresentation.lean` -/

section
open Finsupp
section Semiring
variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
end Semiring
section Ring
section
universe u v
variable (R : Type u) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]
end
variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {R M N}
variable {ι} [Finite ι]
namespace Module.FinitePresentation
end Module.FinitePresentation
end Ring
section CommRing
variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]
open TensorProduct LinearMap
section Pi

variable {ι : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

variable (R) in
lemma Module.piRightHom_bijective_of_finite_free (κ : Type*) [Finite κ] :
    Function.Bijective (piRightHom R R (κ → R) P) := by
  classical
  have := Fintype.ofFinite κ
  have key : ⇑(LinearEquiv.piCongrRight fun i ↦
        TensorProduct.comm R (κ → R) (P i) ≪≫ₗ piScalarRight R R (P i) κ) ∘
        ⇑(piRightHom R R (κ → R) P) =
      Equiv.piComm _ ∘ ⇑(TensorProduct.comm R (κ → R) (Π i, P i) ≪≫ₗ
        piScalarRight R R (Π i, P i) κ) := by
    ext x : 1
    induction x with
    | tmul a q => ext; simp [Function.swap]
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
      rfl
  rw [← EquivLike.comp_bijective _ (LinearEquiv.piCongrRight fun i ↦
    TensorProduct.comm R (κ → R) (P i) ≪≫ₗ piScalarRight R R (P i) κ), key]
  exact (Equiv.bijective _).comp (LinearEquiv.bijective _)

variable (R M) in
/-- If `M` is a finitely presented `R`-module, then for any family of `R`-modules `P i`, the
canonical map `M ⊗[R] (Π i, P i) → Π i, M ⊗[R] P i` is bijective. -/
@[stacks 059K "(1) ⇒ (2)"]
theorem Module.FinitePresentation.piRightHom_bijective [Module.FinitePresentation R M] :
    Function.Bijective (piRightHom R R M P) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  exact bijective_of_surjective_of_bijective_of_right_exact (g.rTensor _) (f.rTensor _)
    (piMap fun i ↦ g.rTensor (P i)) (piMap fun i ↦ f.rTensor (P i)) _ _ _
    (TensorProduct.ext' fun _ _ ↦ by ext; simp) (TensorProduct.ext' fun _ _ ↦ by ext; simp)
    (rTensor_exact _ hfg hf) (Function.Exact.piMap fun i ↦ rTensor_exact _ hfg hf)
    (piRightHom_bijective_of_finite_free R P _).2 (piRightHom_bijective_of_finite_free R P _)
    (rTensor_surjective _ hf)
    (by simpa using Function.Surjective.piMap fun i ↦ rTensor_surjective _ hf)

end Pi

end CommRing
end
