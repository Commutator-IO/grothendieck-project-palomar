module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Grothendieck.Folder85

open Matrix

variable {R : Type*} [CommRing R]

/-- The invariant `A` of pages 23 and 27 for `PGL₂`: `(Tr g)² / det g − 2`,
for a lift `g ∈ GL₂(R)`. -/
noncomputable def invA (g : Matrix (Fin 2) (Fin 2) R) : R :=
  g.trace ^ 2 * Ring.inverse g.det - 2

/-- `g` is nowhere scalar: its image in `PGL₂(k(s))` is not `1` for any point
`s` of `Spec R`, that is, `b`, `c`, `a − d` generate the unit ideal. -/
def NullePartScalaire (g : Matrix (Fin 2) (Fin 2) R) : Prop :=
  Ideal.span {g 0 1, g 1 0, g 0 0 - g 1 1} = ⊤

/-- **Pages 10, 30, 40.** If `g ∈ GL₂(R)` is nowhere scalar and `g⁵` is scalar
(the image of `g` in `PGL₂` has order 5 on every fibre), then `A(g)` is a root
of `T² + T − 1`. Over any commutative ring. -/
theorem sq_add_sub_of_pow_five (g : Matrix (Fin 2) (Fin 2) R) (hg : IsUnit g.det)
    (hns : NullePartScalaire g)
    {c : R} (h5 : g ^ 5 = c • (1 : Matrix (Fin 2) (Fin 2) R)) :
    invA g ^ 2 + invA g - 1 = 0 := by
  sorry

end Grothendieck.Folder85
