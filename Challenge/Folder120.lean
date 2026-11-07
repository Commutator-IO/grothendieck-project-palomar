module

public import Mathlib

@[expose] public section

namespace Grothendieck.Folder120

open Function

universe u

/-- The axioms (M′1)–(M′4) of page 2 (with (M′) for finite index sets, page 4): a family
`M I ⊂ 𝔓(R^I)` of tame subsets, `u^* x = x ∘ u`. -/
structure TameModel (R : Type u) where
  /-- The tame subsets of `R^I`. -/
  M : (I : Type) → Set (Set (I → R))
  /-- (M′1) direct image by `u^*`. -/
  m1 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J) {A : Set (J → R)},
    A ∈ M J → (fun x : J → R => x ∘ u) '' A ∈ M I
  /-- (M′2) preimage by `u^*` for `u` surjective. -/
  m2 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J), Surjective u →
    ∀ {B : Set (I → R)}, B ∈ M I → (fun x : J → R => x ∘ u) ⁻¹' B ∈ M J
  /-- (M′3) cut of a tame subset by a preimage. -/
  m3 : ∀ {I J : Type} [Finite I] [Finite J] (u : I → J) {A : Set (J → R)}
    {B : Set (I → R)}, A ∈ M J → B ∈ M I → (fun x : J → R => x ∘ u) ⁻¹' B ∩ A ∈ M J
  /-- (M′4) products, `R^I × R^J = R^{I ⊔ J}`. -/
  m4 : ∀ {I J : Type} [Finite I] [Finite J] {A : Set (I → R)} {B : Set (J → R)},
    A ∈ M I → B ∈ M J → {x : I ⊕ J → R | x ∘ Sum.inl ∈ A ∧ x ∘ Sum.inr ∈ B} ∈ M (I ⊕ J)

/-- The graph over `X ⊂ R^I` of a family `F : R^I → R^K`, a subset of `R^{I ⊔ K}`. -/
def graphOn {R : Type u} {I K : Type} (X : Set (I → R)) (F : (I → R) → K → R) :
    Set (I ⊕ K → R) :=
  {y | y ∘ Sum.inl ∈ X ∧ ∀ k, y (Sum.inr k) = F (y ∘ Sum.inl) k}

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- A tame function on `X`: its graph over `X` is a tame subset of `R^{I ⊔ 1}`. -/
def IsTameFun {I : Type} (X : Set (I → R)) (f : (I → R) → R) : Prop :=
  graphOn X (fun x (_ : Unit) => f x) ∈ T.M (I ⊕ Unit)

/-- The tame points `R₀ = {c | {c} ∈ 𝓜₁}`. -/
def R0 : Set R := {c | {fun _ : Unit => c} ∈ T.M Unit}

/-- (M11) b) (page 20): `x - y` and `xy` are tame on every tame `A ⊂ R²`. -/
def RingOps [CommRing R] : Prop :=
  ∀ A ∈ T.M (Fin 2), T.IsTameFun A (fun z => z 0 - z 1) ∧ T.IsTameFun A (fun z => z 0 * z 1)

/-- (M11) in full, for a field (page 20): `0` and `1` tame points, b), and a tame set
containing the inverses of a tame `A ⊂ R^*`. -/
structure M11 [Field R] : Prop where
  zero_mem : (0 : R) ∈ T.R0
  one_mem : (1 : R) ∈ T.R0
  ringOps : T.RingOps
  inv : ∀ A ∈ T.M Unit, (∀ x ∈ A, x () ≠ 0) →
    ∃ B ∈ T.M Unit, ∀ x ∈ A, (fun _ => (x ())⁻¹) ∈ B

end TameModel

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- The Proposition under (M11) for a field, as the page states it. -/
theorem exists_separating_family_of_field [Field R] (h11 : T.M11) {I : Type} [Finite I]
    {X : Set (I → R)} (hX : X ∈ T.M I) {A : Type} [Finite A] (f : A → (I → R) → R)
    (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R) (he : ∀ a, e a ∈ T.R0) :
    ∃ (C : Type) (_ : Finite C) (h : C → (I → R) → R), (∀ c, T.IsTameFun X (h c)) ∧
      (∀ x, (∀ c, h c x = 0) ↔ ∀ a, f a x = e a) ∧
      ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y → ∃ c, h c x ≠ h c y := by
  sorry

end TameModel

end Grothendieck.Folder120
