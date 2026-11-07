module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section

namespace Grothendieck.Folder107

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A relative cylinder on `i : X ⟶ X'`: precylinders `X ⊗ J`, `X' ⊗ J` and a
map `i ⊗ J : X ⊗ J ⟶ X' ⊗ J` compatible with both ends (folder 107, p. 22). -/
structure RelativeCylinder {X X' : C} (i : X ⟶ X') where
  /-- The cylinder `X ⊗ J`. -/
  P : Precylinder X
  /-- The cylinder `X' ⊗ J`. -/
  P' : Precylinder X'
  /-- The map `i ⊗ J`. -/
  iJ : P.I ⟶ P'.I
  w₀ : P.i₀ ≫ iJ = i ≫ P'.i₀
  w₁ : P.i₁ ≫ iJ = i ≫ P'.i₁

attribute [reassoc] RelativeCylinder.w₀ RelativeCylinder.w₁

/-- `H` is a homotopy from `f` to `f'` on the precylinder `P`. -/
def IsHomotopy {A Y : C} (P : Precylinder A) (H : P.I ⟶ Y) (f f' : A ⟶ Y) : Prop :=
  P.i₀ ≫ H = f ∧ P.i₁ ≫ H = f'

section ModelCategory

variable [ModelCategory C] {X X' Y Y' : C} {i : X ⟶ X'} (R : RelativeCylinder i)

/-- **Pages 20 and 22 in a model category.** With `p` a fibration and the
corner map of the relative cylinder a trivial cofibration, the diagonal `φ`
can be rectified if and only if the homotopies can be chosen compatible. -/
theorem rectification_modelCategory (p : Y ⟶ Y') [Fibration p]
    [Cofibration (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    [WeakEquivalence (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (φ : X' ⟶ Y) :
    (∃ (φbar : X' ⟶ Y) (K : R.P'.I ⟶ Y),
        i ≫ φbar = g ∧ φbar ≫ p = g' ∧ IsHomotopy R.P' K φ φbar) ↔
      ∃ (k : R.P.I ⟶ Y) (h : R.P'.I ⟶ Y'),
        IsHomotopy R.P k (i ≫ φ) g ∧ IsHomotopy R.P' h (φ ≫ p) g' ∧ k ≫ p = R.iJ ≫ h := by
  sorry

end ModelCategory

end Grothendieck.Folder107
