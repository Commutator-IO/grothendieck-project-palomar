module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Grothendieck.Folder16

open LieModule

section Projecteurs

variable {E : Type*} [Ring E]

/-- `x` is homogeneous of degree `d` for the grading given by the idempotents `π`:
`π_b x π_a = 0` unless `b = a + d`. -/
def Homogene (π : ℤ → E) (d : ℤ) (x : E) : Prop :=
  ∀ a b, b ≠ a + d → π b * x * π a = 0

/-- The grading data: `π` orthogonal idempotents of sum `1`, zero outside `[0, 2n]`. -/
structure Graduation (π : ℤ → E) (n : ℕ) : Prop where
  idem : ∀ a, π a * π a = π a
  orth : ∀ a b, a ≠ b → π a * π b = 0
  supp : ∀ a, a ∉ Finset.Icc (0 : ℤ) (2 * n) → π a = 0
  sum : ∑ a ∈ Finset.Icc (0 : ℤ) (2 * n), π a = 1

variable {π : ℤ → E} {n : ℕ}

end Projecteurs

section DecompositionPrimitive

variable {E : Type*} [Ring E] {π : ℤ → E} {n : ℕ}

/-- The primitive decomposition `M^a = ⊕ L^β P^j` (`j + 2β = a`), read in the ring `E`:
orthogonal idempotents `p j β` of sum `1`, `p j β` living in degree `j + 2β`, `L` carrying
the block `(j, β)` to `(j, β + 1)` and killing the top `(j, n - j)` of each chain, and the
image of `p j β` contained in `L^β` times the image of `p j 0` (`L^β P^j`, not merely a
complement). -/
structure DecompositionPrimitive (π : ℤ → E) (n : ℕ) (L : E) (p : ℕ → ℕ → E) : Prop where
  idem : ∀ j ≤ n, ∀ β ≤ n - j, p j β * p j β = p j β
  orth : ∀ j ≤ n, ∀ β ≤ n - j, ∀ k ≤ n, ∀ γ ≤ n - k, (j, β) ≠ (k, γ) → p j β * p k γ = 0
  sum : ∑ j ∈ Finset.range (n + 1), ∑ β ∈ Finset.range (n - j + 1), p j β = 1
  left : ∀ j ≤ n, ∀ β ≤ n - j, ∀ a : ℤ,
    π a * p j β = if a = (j : ℤ) + 2 * β then p j β else 0
  right : ∀ j ≤ n, ∀ β ≤ n - j, ∀ a : ℤ,
    p j β * π a = if a = (j : ℤ) + 2 * β then p j β else 0
  comm : ∀ j ≤ n, ∀ β < n - j, L * p j β = p j (β + 1) * L
  top : ∀ j ≤ n, L * p j (n - j) = 0
  image : ∀ j ≤ n, ∀ β ≤ n - j, ∃ y, p j β = L ^ β * p j 0 * y

/-- **Pages 4–12, the criterion of no. 6, (1) ⇒ (2) and (3), over `ℤ` and with no module**
(finding `16-graded-ring-lefschetz-criterion`). In a ring `E` graded by orthogonal idempotents
`π_a` (`a ∈ [0, 2n]`), let `ℰ` be a subring containing `L` of degree `2` and one-sided inverses
`wᵢ` of `L^{n-i}` (`(6.3)ᵢ`), and let `p` be the primitive decomposition, read in `E`. Then the
grading projectors, every primitive projector and the pseudo-inverse `Λ` lie in `ℰ`; `Λ` has
degree `-2` and satisfies `(6.7)`. -/
theorem critere_lefschetz (ℰ : Subring E) (G : Graduation π n) {L : E} (hLE : L ∈ ℰ)
    (hL : Homogene π 2 L) {w : ℕ → E} (hwE : ∀ i ≤ n, w i ∈ ℰ)
    (hw : ∀ i ≤ n, Homogene π (-(2 * ((n : ℤ) - i))) (w i))
    (h₁ : ∀ i ≤ n, w i * L ^ (n - i) * π i = π i)
    (h₂ : ∀ i ≤ n, L ^ (n - i) * w i * π (2 * n - i) = π (2 * n - i))
    {p : ℕ → ℕ → E} (D : DecompositionPrimitive π n L p) :
    (∀ a, π a ∈ ℰ) ∧ (∀ j ≤ n, ∀ β ≤ n - j, p j β ∈ ℰ) ∧
      ∃ Λ ∈ ℰ, Homogene π (-2) Λ ∧
        L * Λ = 1 - ∑ j ∈ Finset.range (n + 1), p j 0 ∧
        Λ * L = 1 - ∑ j ∈ Finset.range (n + 1), p j (n - j) := by
  sorry

end DecompositionPrimitive

end Grothendieck.Folder16
