module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/flat-prod-pi`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/flat-prod-pi`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/RingTheory/Flat/Basic.lean` -/

universe v' u v w
open TensorProduct
namespace Module
open Function (Injective Surjective)
open LinearMap Submodule DirectSum
section Semiring
variable {R : Type u} {M : Type v} {N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
namespace Flat
section DirectSum
variable {ι : Type v} {M : ι → Type w} [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]
theorem pi_iff [Finite ι] : Flat R (Π i, M i) ↔ ∀ i, Flat R (M i) := by
  classical
  have := Fintype.ofFinite ι
  rw [← directSum_iff]
  exact equiv_iff (linearEquivFunOnFintype R ι M).symm

/-- A finite product of flat `R`-modules is flat. -/
instance pi [Finite ι] [∀ i, Flat R (M i)] : Flat R (Π i, M i) := pi_iff.mpr ‹_›

end DirectSum
theorem prod_iff : Flat R (M × N) ↔ Flat R M ∧ Flat R N := by
  have key {P : Type u} [AddCommMonoid P] [Module R P] (Q : Submodule R P) :
      Function.Injective (Q.subtype.rTensor (M × N)) ↔
        Function.Injective (Q.subtype.rTensor M) ∧ Function.Injective (Q.subtype.rTensor N) := by
    have : (prodRight R R P M N).toLinearMap ∘ₗ Q.subtype.rTensor (M × N) =
        (Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N) ∘ₗ
          (prodRight R R Q M N).toLinearMap := by
      ext <;> simp
    simpa [coe_prodMap, Prod.map_injective] using congr(Function.Injective ⇑$this)
  simp_rw [iff_rTensor_injectiveₛ, key, forall_and]

/-- The product of two flat `R`-modules is flat. -/
instance prod [Flat R M] [Flat R N] : Flat R (M × N) := prod_iff.mpr ⟨‹_›, ‹_›⟩

section Algebra
variable {S : Type*} [Semiring S] [Algebra R S]
variable (R S M)
end Algebra
end Flat
end Semiring
namespace Flat
variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
end Flat
end Module
section Injective
variable {R S A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CommSemiring S] [Algebra S A] [SMulCommClass R S A]
namespace Algebra.TensorProduct
end Algebra.TensorProduct
variable (A) [Module.Flat R A] {M : Type*} [AddCommMonoid M] [Module R M] (p : Submodule R M)
namespace Submodule
end Submodule
end Injective
section Nontrivial
variable (R : Type*) [CommSemiring R]
namespace TensorProduct
variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
variable {R M N}
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
variable {ι κ : Type*} {v : ι → M} {w : κ → N} {s : Set ι} {t : Set κ}
variable (p : Submodule R M) (q : Submodule R N)
end TensorProduct
namespace Algebra.TensorProduct
variable (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
end Algebra.TensorProduct
end Nontrivial
namespace IsTensorProduct
variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {M₁ M₂ N₁ N₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]
  {f : M₁ →ₗ[R] M₂ →ₗ[R] M} {g : N₁ →ₗ[R] N₂ →ₗ[R] N}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂)
end IsTensorProduct
section IsSMulRegular
variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Module.Flat R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
end IsSMulRegular
