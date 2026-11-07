module

public import Mathlib

@[expose] public section


/-!
# Backport of the mathlib4 branch `mycaule/isAdicComplete-of-isNilpotent`

Declarations a proof of this repository needed and that were proposed to mathlib4 from
the fork mycaule/mathlib4, branch `mycaule/isAdicComplete-of-isNilpotent`, closed upstream on
2026-10-22. They keep their mathlib names, against the pinned Mathlib; drop a
declaration once Mathlib has it.
-/


/-! ## From `Mathlib/RingTheory/AdicCompletion/Basic.lean` -/

section
open Submodule Ideal Quotient
variable {R S T : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {I M}
variable (I M)
namespace IsHausdorff
variable {I M}
end IsHausdorff
namespace Hausdorffification
variable {I M}
variable (I M)
variable {M} [h : IsHausdorff I N]
end Hausdorffification
namespace IsPrecomplete
end IsPrecomplete
namespace AdicCompletion
variable {I M}
variable (I M)
variable {I M}
variable (I M)
variable {I M}
variable (I M)
namespace AdicCauchySequence
variable {I M}
end AdicCauchySequence
variable {M}
section Bijective
variable {I}
variable (I M)
variable [IsAdicComplete I M]
variable {M}
end Bijective
end AdicCompletion
namespace IsAdicComplete
open AdicCompletion
section lift
variable [IsAdicComplete I N]
variable {M}
end lift
namespace StrictMono
variable {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ (a n) • ⊤ : Submodule R N))
variable {I M}
variable (hf : ∀ {m}, factorPow I N (ha.monotone m.le_succ) ∘ₗ (f (m + 1)) = f m)
variable [IsAdicComplete I N]
variable (I)
end StrictMono
variable {I} in
theorem of_isNilpotent (hI : IsNilpotent I) : IsAdicComplete I M := by
  obtain ⟨k, hk⟩ := hI
  have h {n : ℕ} (hn : k ≤ n) : (I ^ n • ⊤ : Submodule R M) = ⊥ := by
    rw [le_bot_iff.1 ((Ideal.pow_le_pow_right hn).trans_eq hk), Submodule.bot_smul]
  refine { haus' x hx := ?_, prec' f hf := ⟨f k, fun n ↦ ?_⟩ }
  · simpa [h le_rfl, SModEq.zero] using hx k
  · rcases le_total n k with hn | hn
    · exact hf hn
    · rw [SModEq.bot.1 (h le_rfl ▸ hf hn : f k ≡ f n [SMOD (⊥ : Submodule R M)])]

open Finset
end IsAdicComplete
end

/-! ## From `Mathlib/RingTheory/AdicCompletion/Noetherian.lean` -/

section
open IsLocalRing Module
variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]
end
