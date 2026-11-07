module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder156_3

open Set

section Defs

variable {α : Type*} [PartialOrder α]

/-- `x` and `y` are comparable. -/
def Cmp (x y : α) : Prop := x ≤ y ∨ y ≤ x

/-- Strict betweenness `𝓡(a, b, c)`: `a < b < c` or `a > b > c` (page 11). -/
def Btw (a b c : α) : Prop := (a < b ∧ b < c) ∨ (c < b ∧ b < a)

/-- `t ∈ C({a, b})`: `t ∉ {a, b}` and `{a, b, t}` is a chain (page 14). -/
def InC (a b t : α) : Prop := t ≠ a ∧ t ≠ b ∧ Cmp t a ∧ Cmp t b

/-- `s` and `t` lie in the same piece of `C({a, b})`: both below `a` and `b`,
both strictly between them, or both above them (pages 8 and 14). The relation
is symmetric in `a, b`, so it depends only on the pair. -/
def SamePiece (a b s t : α) : Prop :=
  (s < a ∧ s < b ∧ t < a ∧ t < b) ∨ (Btw a s b ∧ Btw a t b) ∨ (a < s ∧ b < s ∧ a < t ∧ b < t)

/-- A tronçon ordonné (page 8). -/
structure Troncon (α : Type*) [PartialOrder α] : Prop where
  /-- a) `L_{>a}` is directed downwards. -/
  dir_down : ∀ a x y : α, a < x → a < y → ∃ z, a < z ∧ z ≤ x ∧ z ≤ y
  /-- a′) `L_{<a}` is directed upwards. -/
  dir_up : ∀ a x y : α, x < a → y < a → ∃ z, x ≤ z ∧ y ≤ z ∧ z < a
  /-- b) `L` is directed downwards … -/
  low : ∀ x y : α, ∃ z, z ≤ x ∧ z ≤ y
  /-- … and upwards. -/
  high : ∀ x y : α, ∃ z, x ≤ z ∧ y ≤ z
  /-- c) `L` is dense (« divisible »). -/
  dense : ∀ x y : α, x < y → ∃ z, x < z ∧ z < y
  /-- d) `card L > 1`. -/
  card : ∃ x y : α, x ≠ y

end Defs

section Transport

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- The data of page 14 preserved by a bijection `e`: comparability, and for each
comparable pair `ε` the partition of `C(ε)` into its pieces. -/
structure PreservesCuts (e : α ≃ β) : Prop where
  cmp : ∀ x y, Cmp (e x) (e y) ↔ Cmp x y
  piece : ∀ a b, a ≠ b → Cmp a b → ∀ s t, InC a b s → InC a b t →
    (SamePiece (e a) (e b) (e s) (e t) ↔ SamePiece a b s t)

end Transport

section Order

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

/-- **The finding, pages 11–15.** A bijection between tronçons ordonnés that
preserves comparability and, for every comparable pair `ε`, the partition of
`C(ε)` into its pieces, is an order isomorphism or an order anti-isomorphism.
Only conditions b) and c) of page 8 are used. -/
theorem order_of_cuts (hα : Troncon α) (hβ : Troncon β) {e : α ≃ β}
    (he : PreservesCuts e) :
    (∀ x y, e x ≤ e y ↔ x ≤ y) ∨ (∀ x y, e y ≤ e x ↔ x ≤ y) := by
  sorry

end Order

end Grothendieck.Folder156_3
