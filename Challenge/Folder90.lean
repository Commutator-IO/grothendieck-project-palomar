module

public import Mathlib

@[expose] public section

open Polynomial TensorProduct

namespace Grothendieck.Folder90

variable (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]

variable {R K}

variable (R K) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

section Components

variable {A : Type*} [CommRing A] (π : A)

/-- **The criterion for `A` reduced and Noetherian**: `⋂ₙ πⁿA = 0` if and only if every
irreducible component of `Spec A` meets the special fibre `V(π)`. -/
theorem iInf_pow_eq_bot_iff [IsNoetherianRing A] [IsReduced A] :
    ⨅ n : ℕ, Ideal.span {π} ^ n = ⊥ ↔ ∀ p ∈ minimalPrimes A, p ⊔ Ideal.span {π} ≠ ⊤ := by
  sorry

end Components

end Grothendieck.Folder90
