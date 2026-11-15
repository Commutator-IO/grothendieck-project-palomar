module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/isNoetherianRing-iff-finitePresentation`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4,
branch `mycaule/isNoetherianRing-iff-finitePresentation`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/Algebra/Module/FinitePresentation.lean` -/

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
universe v in
variable (R) in
/-- A ring `R` is Noetherian if and only if every finitely generated `R`-module is finitely
presented. It suffices to consider modules in any universe in which `R` is small. -/
theorem isNoetherianRing_iff_forall_finitePresentation [Small.{v} R] :
    IsNoetherianRing R ↔ ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Module.FinitePresentation R M := by
  refine ⟨fun _ M _ _ _ ↦ Module.finitePresentation_of_finite R M, fun h ↦ ?_⟩
  refine (isNoetherianRing_iff_ideal_fg R).2 fun I ↦ ?_
  let e := Shrink.linearEquiv.{v} R (R ⧸ I)
  have := Module.Finite.equiv e.symm
  have := h (Shrink.{v} (R ⧸ I))
  have := Module.FinitePresentation.of_equiv e
  have hI := Module.FinitePresentation.fg_ker I.mkQ I.mkQ_surjective
  rw [Submodule.ker_mkQ] at hI
  exact hI

end Ring
section CommRing
variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]
open TensorProduct LinearMap
end CommRing
