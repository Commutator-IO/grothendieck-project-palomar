module

public import Mathlib

@[expose] public section

open CategoryTheory Opposite

namespace Grothendieck.Folder55

universe u

variable {X : TopCat.{u}} {F : TopCat.Presheaf (Type u) X}

/-- A subsheaf of a presheaf of types `F`: for each open `U` a set of sections over `U`,
stable under restriction, and *local* — a section lies in it as soon as it does locally. -/
structure Subsheaf (F : TopCat.Presheaf (Type u) X) where
  /-- The sections over `U` lying in the subsheaf. -/
  sections : ∀ U : Opens X, Set (F.obj (op U))
  restrict : ∀ {U V : Opens X} (h : V ≤ U) {s : F.obj (op U)},
    s ∈ sections U → F.map (homOfLE h).op s ∈ sections V
  isLocal : ∀ (U : Opens X) (s : F.obj (op U)),
    (∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ F.map (homOfLE h).op s ∈ sections V) →
      s ∈ sections U

namespace Subsheaf

@[ext]
theorem ext {S T : Subsheaf F} (h : ∀ U, S.sections U = T.sections U) : S = T := by
  cases S; cases T; congr; exact funext h

instance : PartialOrder (Subsheaf F) where
  le S T := ∀ U, S.sections U ⊆ T.sections U
  le_refl _ _ := subset_rfl
  le_trans _ _ _ h₁ h₂ U := (h₁ U).trans (h₂ U)
  le_antisymm _ _ h₁ h₂ := ext fun U => (h₁ U).antisymm (h₂ U)

/-- `S` and `T` agree on the open `W`: they have the same sections over every open of `W`. -/
def AgreeOn (S T : Subsheaf F) (W : Opens X) : Prop :=
  ∀ V : Opens X, V ≤ W → S.sections V = T.sections V

/-- The germs at `x` of the sections of `S`, a subset of the stalk `F_x`. -/
def germs (S : Subsheaf F) (x : X) : Set (F.stalk x) :=
  {g | ∃ (U : Opens X) (hx : x ∈ U) (s : F.obj (op U)), s ∈ S.sections U ∧ F.germ U x hx s = g}

end Subsheaf

open Subsheaf

/-- **Lemme B, with the identity principle replaced by the uniformity it is meant to give.**
On a quasi-compact space, let `S` be an increasing sequence of subsheaves. Suppose that
* at every point the germs stabilise (hypothesis (iv): see `germs_stabilize_of_noetherian`);
* (uniformity) for every point `x` and every index `k`, there is an open neighbourhood `W` of
  `x` such that every later `S l` with the same germs at `x` as `S k` agrees with `S k` on `W`.
Then the sequence is stationary. -/
theorem stationary_of_germs [CompactSpace X] (S : ℕ → Subsheaf F) (hS : Monotone S)
    (hgerm : ∀ x : X, ∃ k₀, ∀ k ≥ k₀, (S k).germs x = (S k₀).germs x)
    (huniform : ∀ (x : X) (k : ℕ), ∃ W : Opens X, x ∈ W ∧
      ∀ l ≥ k, (S l).germs x = (S k).germs x → AgreeOn (S l) (S k) W) :
    ∃ k₀, ∀ k ≥ k₀, S k = S k₀ := by
  sorry

end Grothendieck.Folder55
