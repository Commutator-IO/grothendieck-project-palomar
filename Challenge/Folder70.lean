module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.FieldTheory.Relrank
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

@[expose] public section

namespace Grothendieck.Folder70

section General

variable {R : Type*} [CommRing R] (α : R)

/-- The antipodism `ι` of page 91, (17). -/
def iota (p : R × R × R) : R × R × R :=
  ((-1 - α) - p.1, 1 - (-1 - α) - p.2.1, 1 - (-1 - α) - p.2.2)

/-- The twelve vertices of page 75 in the order `s₀, s₁, s₂, s₃, s'₃, s''₃` and their
antipodes `ι s₀, …, ι s''₃`. -/
def vert : Fin 12 → R × R × R :=
  ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (-1 - α, -(-1 - α), 1), (0, -(-1 - α), 1),
    iota α (0, 0, 0), iota α (1, 0, 0), iota α (0, 1, 0), iota α (0, 0, 1),
    iota α (-1 - α, -(-1 - α), 1), iota α (0, -(-1 - α), 1)]

variable {α}

end General

end Grothendieck.Folder70

namespace Grothendieck.Folder70

section Quadric

open Matrix

variable {R : Type*} [CommRing R] {α : R}

/-- A quadratic function `a x² + b y² + c z² + u yz + v zx + w xy + d x + e y + f z + k` on
`R³`, by its ten coefficients. -/
@[ext] structure QuadFn (R : Type*) where
  (a b c u v w d e f k : R)

/-- The value of a quadratic function at a point. -/
def QuadFn.eval (Q : QuadFn R) (p : R × R × R) : R :=
  Q.a * p.1 ^ 2 + Q.b * p.2.1 ^ 2 + Q.c * p.2.2 ^ 2 + Q.u * (p.2.1 * p.2.2)
    + Q.v * (p.2.2 * p.1) + Q.w * (p.1 * p.2.1) + Q.d * p.1 + Q.e * p.2.1 + Q.f * p.2.2 + Q.k

/-- A scalar multiple of a quadratic function. -/
def QuadFn.smul (r : R) (Q : QuadFn R) : QuadFn R :=
  ⟨r * Q.a, r * Q.b, r * Q.c, r * Q.u, r * Q.v, r * Q.w, r * Q.d, r * Q.e, r * Q.f, r * Q.k⟩

variable (α) in
/-- The coefficients of the invariant function `q` of pages 95 and 101. -/
def qFn : QuadFn R := ⟨1, 1, 1, -α, 1, 1, -1, -1, -1, 0⟩

/-- **Page 101: uniqueness of the quadric.** Over any commutative ring with `α² + α − 1 = 0`,
a quadratic function vanishing at the nine vertices `s₀, s₁, s₂, s₃, s'₃, s''₃, ι s₀, ι s₁,
ι s₂` is `a · q`, `a` its coefficient of `x²`: the `9 × 9` minor of the linear system is
`13α + 21`, a unit of `ℤ[α]` (of inverse `13α − 8`). -/
theorem quadric_unique (h : α ^ 2 + α - 1 = 0) (Q : QuadFn R)
    (hQ : ∀ i : Fin 12, i.val < 9 → Q.eval (vert α i) = 0) : Q = QuadFn.smul Q.a (qFn α) := by
  sorry

end Quadric

end Grothendieck.Folder70
