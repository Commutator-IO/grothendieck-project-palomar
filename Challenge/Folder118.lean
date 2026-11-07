module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder118

open MulAction

variable (G : Type*) [Group G]

/-- `f : X → Y` is in `𝒲_A`, `A = BG`, read through the action groupoids: bijective on
orbits, and `Stab(f x) ⊆ Stab(x)` (the other inclusion always holds). -/
def IsWeq {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) : Prop :=
  (∀ y : Y, ∃ (x : X) (g : G), g • f x = y) ∧
  (∀ (x x' : X) (g : G), g • f x = f x' → ∃ h : G, h • x = x') ∧
  (∀ (x : X) (g : G), g • f x = f x → g • x = x)

/-- `X//G` is aspherical: non-empty, connected, with trivial automorphism groups. -/
def Aspherical (X : Type*) [MulAction G X] : Prop :=
  Nonempty X ∧ (∀ x y : X, ∃ g : G, g • x = y) ∧ ∀ (x : X) (g : G), g • x = x → g = 1

variable {G}

/-- The product of two maps of `G`-sets. -/
def prodHom {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] (f : X →[G] Y) (f' : X' →[G] Y') : X × X' →[G] Y × Y' where
  toFun p := (f p.1, f' p.2)
  map_smul' g p := by simp [map_smul]

/-- **The answer « Non » of page 35**, for `A = BG`, `G ≠ 1`: `𝒲_A` is stable under
products, but neither `A` nor `a × a` is aspherical. -/
theorem answer_page_35 [Nontrivial G] :
    (∀ {X Y X' Y' : Type} [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
      (f : X →[G] Y) (f' : X' →[G] Y'), IsWeq G f → IsWeq G f' → IsWeq G (prodHom f f')) ∧
    ¬ Aspherical G PUnit ∧ ¬ Aspherical G (G × G) := by
  sorry

end Grothendieck.Folder118
