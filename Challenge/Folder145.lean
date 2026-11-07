module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder145

open DihedralGroup

/-- A profinite integer, as a family of residues: `p n ∈ ZMod n` for `n ≠ 0`, compatible
under reduction. (The value at `n = 0` plays no role.) -/
def Compatible (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ m n : ℕ, n ≠ 0 → ∀ h : m ∣ n, ZMod.castHom h (ZMod m) (p n) = p m

/-- `x ^ p` for `p ∈ ℤ̂` in a finite group: the power by the residue of `p` modulo the
order of the group. -/
def hatPow {G : Type*} [Group G] [Fintype G] (p : ∀ n : ℕ, ZMod n) (x : G) : G :=
  x ^ (p (Fintype.card G)).val

/-- Relation (14) of page 35, `l_∞^p l₁^p l₀^p = 1` under `l_∞ l₁ l₀ = 1`, read in every
finite quotient of the free profinite group on `l₀, l₁`. -/
def Rel14 (p : ∀ n : ℕ, ZMod n) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (x y z : G),
    z * y * x = 1 → hatPow p z * hatPow p y * hatPow p x = 1

/-- The page's form: `p` a unit of `ℤ̂` (each residue a unit). -/
theorem rel14_unit_iff (p : ∀ n : ℕ, ZMod n) (hp : Compatible p)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (p n)) :
    Rel14 p ↔ ∀ n : ℕ, n ≠ 0 → p n = 1 := by
  sorry

end Grothendieck.Folder145
