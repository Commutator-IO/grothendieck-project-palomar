module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder100.Baire

open IsLocalRing PrimeSpectrum

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

variable [IsAdicComplete (maximalIdeal R) R]

/-- The Proposition of page 36 for any countable index set. -/
theorem exists_finite_subcover_of_countable {ι : Type*} [Countable ι]
    (Z : ι → Set (PrimeSpectrum R)) (hZ : ∀ i, IsClosed (Z i))
    (hcov : ∀ x : PrimeSpectrum R, Order.coheight x ≤ 1 → x ∈ ⋃ i, Z i) :
    ∃ s : Finset ι, ⋃ i ∈ s, Z i = Set.univ := by
  sorry

end Grothendieck.Folder100.Baire
