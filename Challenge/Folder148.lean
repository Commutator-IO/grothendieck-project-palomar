module

public import Mathlib

@[expose] public section

open Set Filter Topology

namespace Grothendieck.Folder148

/-- A circle `ℝ/ℤ` with `r` marked points, given by its lifted marked points: a strictly
increasing `pt : ℤ → ℝ` with `pt (k + r) = pt k + 1`. The marked point `pt k` has label
`k mod r` in the torsor `ℤ/r`. -/
structure Marking (r : ℕ) where
  /-- The lifted marked points. -/
  pt : ℤ → ℝ
  strictMono : StrictMono pt
  periodic : ∀ k, pt (k + r) = pt k + 1

variable {r : ℕ}

end Grothendieck.Folder148

open scoped ContinuousMap

namespace Grothendieck.Folder148

variable {r : ℕ}

/-- The orientation-reversing homeomorphisms `a → a'` of the circle `AddCircle 1` respecting the
markings through the anti-isomorphism `k ↦ c - k`: bijective continuous maps (homeomorphisms,
the circle being compact) admitting a strictly antitone continuous lift, sending the marked
point `p k` to `q (c - k)`. -/
def circleGluings (P Q : Marking r) (c : ℤ) : Set C(UnitAddCircle, UnitAddCircle) :=
  {f | Function.Bijective f ∧ (∃ F : ℝ → ℝ, Continuous F ∧ StrictAnti F ∧ ∀ x : ℝ, f x = F x) ∧
    ∀ k, f (P.pt k) = Q.pt (c - k)}

/-- **Uniqueness of gluing on the circle (pages 55–58).** The orientation-reversing
homeomorphisms of `AddCircle 1` between two circles with `r` marked points realising a given
anti-isomorphism of `ℤ/r`-torsors form a non-empty contractible space. -/
theorem contractibleSpace_circleGluings (P Q : Marking r) (c : ℤ) :
    ContractibleSpace (circleGluings P Q c) := by
  sorry

end Grothendieck.Folder148
