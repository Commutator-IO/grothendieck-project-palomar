module

public import Mathlib

@[expose] public section

open MvPolynomial

namespace Grothendieck.Folder53

variable {K ι : Type*} [Field K]

/-- The polynomial law: `law m a v i = m i (a, v)`, the variables `inl j` for `a`, `inr j`
for `v`. -/
noncomputable def law (m : ι → MvPolynomial (ι ⊕ ι) K) (a v : ι → K) : ι → K :=
  fun i => eval (Sum.elim a v) (m i)

variable [IsAlgClosed K] [Finite ι]

/-- A monoid of `K`-points of an affine variety with a polynomial law, whose left translations
are injective, is a group (the reading of folder 53, page 21, over an algebraically closed
field). -/
theorem isUnit_of_isLeftCancelMul {M : Type*} [Monoid M] [IsLeftCancelMul M]
    (φ : M → ι → K) (hφ : Function.Injective φ) (I : Ideal (MvPolynomial ι K))
    (hI : Set.range φ = zeroLocus K I) (m : ι → MvPolynomial (ι ⊕ ι) K)
    (hm : ∀ x y, φ (x * y) = law m (φ x) (φ y)) (x : M) : IsUnit x := by
  sorry

end Grothendieck.Folder53

open Pointwise
