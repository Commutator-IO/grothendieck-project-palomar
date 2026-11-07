module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

@[expose] public section

open Module Pointwise

namespace Grothendieck.Folder68

/-- `H` is a closed half-space of `V` bounded by the hyperplane `W`: there is a nonzero
linear form `f` with kernel `W` and `H = {f ≥ 0}`. The opposite half-space is `-H`. -/
def IsHalfSpace {V : Type*} [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) (H : Set V) :
    Prop :=
  ∃ f : V →ₗ[ℝ] ℝ, LinearMap.ker f = W ∧ f ≠ 0 ∧ H = {v | 0 ≤ f v}

/-- A *theory of orientation* (page 49): a functor `Ω` from the groupoid of finite-dimensional
real vector spaces (in `Type`) and their linear isomorphisms to two-element sets (a), an
identification `Ω(0) ≃ {±1}` (b), and for every hyperplane `W ⊂ V` and closed half-space `H`
bounded by `W` a Stokes map `St_H : Ω(V) → Ω(W)` (c), natural in `(V, H)`, subject to the two
axioms: `St_H` is bijective, and `St_{-H} = τ ∘ St_H`, which on a two-element set says
`St_{-H} ω ≠ St_H ω`. -/
structure Theory where
  /-- The two-element set `Ω(V)`. -/
  Ω : (V : Type) → [AddCommGroup V] → [Module ℝ V] → [FiniteDimensional ℝ V] → Type
  /-- The action of linear isomorphisms. -/
  map : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂], (V ≃ₗ[ℝ] V₂) → Ω V → Ω V₂
  map_refl : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : Ω V),
    map (LinearEquiv.refl ℝ V) ω = ω
  map_trans : ∀ {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    [AddCommGroup V₃] [Module ℝ V₃] [FiniteDimensional ℝ V₃]
    (e₁ : V₁ ≃ₗ[ℝ] V₂) (e₂ : V₂ ≃ₗ[ℝ] V₃) (ω : Ω V₁), map (e₁.trans e₂) ω = map e₂ (map e₁ ω)
  card : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V], Nat.card (Ω V) = 2
  /-- `Ω(0) ≃ {±1}`. -/
  zero : Ω (Fin 0 → ℝ) ≃ ℤˣ
  /-- The Stokes map of a half-space. -/
  St : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V), IsHalfSpace W H → Ω V → Ω W
  St_natural : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂] (e : V ≃ₗ[ℝ] V₂)
    (W : Submodule ℝ V) (W₂ : Submodule ℝ V₂) (H : Set V) (H₂ : Set V₂)
    (hH : IsHalfSpace W H) (hH₂ : IsHalfSpace W₂ H₂) (hW : W.map (e : V →ₗ[ℝ] V₂) = W₂)
    (_ : e '' H = H₂) (ω : Ω V),
    St W₂ H₂ hH₂ (map e ω) = map (e.ofSubmodules W W₂ hW) (St W H hH ω)
  St_bijective : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H), Function.Bijective (St W H hH)
  St_neg : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H) (hH' : IsHalfSpace W (-H))
    (ω : Ω V), St W (-H) hH' ω ≠ St W H hH ω

/-- A morphism of theories: a natural transformation compatible with b) and c). -/
structure Hom (T T' : Theory) where
  app : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V], T.Ω V → T'.Ω V
  natural : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂] (e : V ≃ₗ[ℝ] V₂) (ω : T.Ω V),
    app V₂ (T.map e ω) = T'.map e (app V ω)
  zero : ∀ ω, T'.zero (app _ ω) = T.zero ω
  stokes : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H) (ω : T.Ω V),
    T'.St W H hH (app V ω) = app W (T.St W H hH ω)

/-- **Theorem b)** (page 49): between two theories of orientation there is exactly one
morphism, and its components are bijective. -/
theorem exists_unique_hom (T T' : Theory) :
    ∃ φ : Hom T T', (∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
      Function.Bijective (φ.app V)) ∧
      ∀ ψ : Hom T T', ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
        ψ.app V = φ.app V := by
  sorry

end Grothendieck.Folder68
