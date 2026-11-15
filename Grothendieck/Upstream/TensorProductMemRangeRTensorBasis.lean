module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/tensorProduct-mem-range-rTensor-basis`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4,
branch `mycaule/tensorProduct-mem-range-rTensor-basis`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/LinearAlgebra/TensorProduct/Basis.lean` -/

noncomputable section
open LinearMap Module
open scoped TensorProduct
section CommSemiring
variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]
namespace Module.Basis
variable (S : Type*) [Semiring S] [Algebra R S]
end Module.Basis
section
variable [DecidableEq ι] [DecidableEq κ]
variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M ⊗[R] N)
lemma TensorProduct.equivFinsuppOfBasisRight_rTensor {P : Type*} [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] P) (x : M ⊗[R] N) :
    equivFinsuppOfBasisRight 𝒞 (f.rTensor N x) =
      (equivFinsuppOfBasisRight 𝒞 x).mapRange f f.map_zero := by
  induction x with
  | tmul m n => ext; simp
  | add x y hx hy => simp [hx, hy, Finsupp.mapRange_add (map_add f)]

/-- Let `𝒞` be a basis of `N`. An element of `P ⊗[R] N` lies in the range of `f.rTensor N` if and
only if each of its coordinates with respect to `𝒞` lies in the range of `f`. -/
lemma TensorProduct.mem_range_rTensor_iff_equivFinsuppOfBasisRight {P : Type*} [AddCommMonoid P]
    [Module R P] (f : M →ₗ[R] P) (x : P ⊗[R] N) :
    x ∈ range (f.rTensor N) ↔ ∀ i, equivFinsuppOfBasisRight 𝒞 x i ∈ range f := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨y, rfl⟩ i
    simp [equivFinsuppOfBasisRight_rTensor]
  choose g hg using h
  rw [← (equivFinsuppOfBasisRight 𝒞).symm_apply_apply x, equivFinsuppOfBasisRight_symm_apply]
  exact Submodule.sum_mem _ fun i _ ↦ ⟨g i ⊗ₜ 𝒞 i, by simp [hg]⟩

end
end CommSemiring
namespace LinearMap
variable {R A M N ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N]
  [IsScalarTower R A N]
end LinearMap
end
