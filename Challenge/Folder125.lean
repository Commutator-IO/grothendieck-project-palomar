module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

namespace Grothendieck.Folder125

section FeuilletIII18

variable {R : Type*} [CommRing R]

/-- **Feuillet 3 (III-18), affine form.** `R` Noetherian, `B` of finite type,
`u : Rⁿ → B` an isomorphism on the germs at `𝔭`: then `u` is an isomorphism over
a neighbourhood `D(f)` of `𝔭`. -/
theorem lemme_III18 [IsNoetherianRing R] {B : Type*} [AddCommGroup B] [Module R B]
    [Module.Finite R B] {n : ℕ} (u : (Fin n → R) →ₗ[R] B) (p : Ideal R) [p.IsPrime]
    (hu : Function.Bijective (LocalizedModule.map p.primeCompl u)) :
    ∃ f : R, f ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) u) := by
  sorry

end FeuilletIII18

end Grothendieck.Folder125
