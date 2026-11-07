module

public import Mathlib
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

@[expose] public section


/-!
# Folder 107: rectification of a relative square (pages 20 and 22)

The modernised reading `transcripts/107/107.modern.tex` (pages 20 to 23)
considers, in a model category, a commutative square `p g = g' i` — in
mathlib's diagrammatic order `g ≫ p = i ≫ g'` — with `i : X ⟶ X'` a cofibration and
`p : Y ⟶ Y'` a fibration, and a diagonal `φ : X' ⟶ Y` making both triangles
commute only up to homotopies

`k : φ i ⟶ g` (a homotopy `X ⊗ J ⟶ Y`), `h : p φ ⟶ g'` (a homotopy `X' ⊗ J ⟶ Y'`).

Page 22 says that « all we have to do is to check that we can choose these
homotopies compatible with `i` and `p` », i.e. `p ∘ k = h ∘ (i ⊗ J)`, and that
when `Y'` is the final object this is automatic. The reading turns this into a
criterion: a diagonal `φ̄`, homotopic to `φ`, making both triangles commute
strictly exists if and only if such compatible homotopies exist.

## Setting

Cylinders are mathlib's `Precylinder`s (an object `I` with two maps
`i₀ i₁ : A ⟶ I`). A *relative cylinder* on `i : X ⟶ X'`
(`RelativeCylinder`) is a precylinder `X ⊗ J` on `X`, a precylinder
`X' ⊗ J` on `X'` and a map `i ⊗ J` between them commuting with both ends.
A homotopy `f ⟶ f'` on a precylinder `P` is a map `H : P.I ⟶ Y` with
`P.i₀ ≫ H = f`, `P.i₁ ≫ H = f'`.

The one homotopical input the argument needs is the *covering homotopy
extension property* of `i ⊗ J` against `p` (`CoveringHomotopyExtension`): a
homotopy on `X'` below, together with a map on `X'` and a homotopy on `X`
above which agree, lift to a homotopy on `X'` above. In a simplicial model
category this is axiom SM7 for the cofibration `i` and the fibration `p`; in
any model category it holds as soon as the corner map
`X ⊗ J ⊔_X X' ⟶ X' ⊗ J` is a trivial cofibration
(`coveringHomotopyExtension_of_trivialCofibration`, from mathlib's `cm4a`).

## Results

* `rectification` (page 22, sufficiency): compatible homotopies `k`, `h`
  give `φ̄` with `i ≫ φ̄ = g`, `φ̄ ≫ p = g'`, and a homotopy `φ ⟶ φ̄` on
  `X' ⊗ J`, which covers `h` and extends `k`.
* `compatible_of_rectification` (the reading's necessity): if `φ̄` exists,
  with a homotopy `K : φ ⟶ φ̄`, then `k = (i ⊗ J) ≫ K` and `h = K ≫ p` are
  compatible homotopies.
* `rectification_iff`: the criterion, as an equivalence.
* `rectification_of_isTerminal` (page 22, « in case `Y'` is final object we
  are evidently through »): with `Y'` terminal, every pair `k`, `h` is
  compatible, so a homotopy `k` alone suffices.
* `rectification_modelCategory`: the same in a mathlib `ModelCategory`, with
  the corner map a trivial cofibration and `p` a fibration.

Not formalised: the version « up to homotopy relative to the ends » of the
margin of page 20 (which needs cylinders on cylinders), the existence of
relative cylinders with a trivially cofibrant corner map in a general model
category (which here is a hypothesis), and the edition's counterexample (the
path fibration over `S¹`) showing that the condition can fail.
-/

namespace Grothendieck.Folder107

open CategoryTheory Limits HomotopicalAlgebra

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

/-- The covering homotopy extension property of `i ⊗ J` against `p`: given
`a : X' ⟶ Y`, a homotopy `b : X ⊗ J ⟶ Y` starting at `i ≫ a`, and a homotopy
`c : X' ⊗ J ⟶ Y'` starting at `a ≫ p` and covering `b`, there is a homotopy
`L : X' ⊗ J ⟶ Y` starting at `a`, extending `b` and covering `c`. -/
def CoveringHomotopyExtension {X X' Y Y' : C} {i : X ⟶ X'} (R : RelativeCylinder i)
    (p : Y ⟶ Y') : Prop :=
  ∀ (a : X' ⟶ Y) (b : R.P.I ⟶ Y) (c : R.P'.I ⟶ Y'),
    R.P.i₀ ≫ b = i ≫ a → R.P'.i₀ ≫ c = a ≫ p → b ≫ p = R.iJ ≫ c →
      ∃ L : R.P'.I ⟶ Y, R.P'.i₀ ≫ L = a ∧ R.iJ ≫ L = b ∧ L ≫ p = c

section

variable {X X' Y Y' : C} {i : X ⟶ X'} {p : Y ⟶ Y'} (R : RelativeCylinder i)

/-- **Page 22, sufficiency.** If the homotopies `k : φ i ⟶ g` and
`h : p φ ⟶ g'` are compatible, `k ≫ p = (i ⊗ J) ≫ h`, then the diagonal `φ`
can be replaced by a homotopic `φ̄` making both triangles commute strictly;
the homotopy `L : φ ⟶ φ̄` extends `k` and covers `h`. -/
theorem rectification (hR : CoveringHomotopyExtension R p) {g : X ⟶ Y} {g' : X' ⟶ Y'}
    (φ : X' ⟶ Y) (k : R.P.I ⟶ Y) (h : R.P'.I ⟶ Y')
    (hk : IsHomotopy R.P k (i ≫ φ) g) (hh : IsHomotopy R.P' h (φ ≫ p) g')
    (hcompat : k ≫ p = R.iJ ≫ h) :
    ∃ (φbar : X' ⟶ Y) (L : R.P'.I ⟶ Y),
      i ≫ φbar = g ∧ φbar ≫ p = g' ∧ IsHomotopy R.P' L φ φbar ∧
        R.iJ ≫ L = k ∧ L ≫ p = h := by
  obtain ⟨L, h₀, h₁, h₂⟩ := hR φ k h hk.1 hh.1 hcompat
  exact ⟨R.P'.i₁ ≫ L, L, by rw [← R.w₁_assoc, h₁, hk.2], by rw [Category.assoc, h₂, hh.2],
    ⟨h₀, rfl⟩, h₁, h₂⟩

/-- **The reading's necessity.** If `φ̄` makes both triangles commute and
`K : φ ⟶ φ̄` is a homotopy on `X' ⊗ J`, then `k = (i ⊗ J) ≫ K` and `h = K ≫ p`
are homotopies `φ i ⟶ g` and `p φ ⟶ g'`, and they are compatible. -/
theorem compatible_of_rectification {g : X ⟶ Y} {g' : X' ⟶ Y'} (φ φbar : X' ⟶ Y)
    (hg : i ≫ φbar = g) (hg' : φbar ≫ p = g') (K : R.P'.I ⟶ Y)
    (hK : IsHomotopy R.P' K φ φbar) :
    IsHomotopy R.P (R.iJ ≫ K) (i ≫ φ) g ∧ IsHomotopy R.P' (K ≫ p) (φ ≫ p) g' ∧
      (R.iJ ≫ K) ≫ p = R.iJ ≫ (K ≫ p) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, Category.assoc _ _ _⟩
  · rw [R.w₀_assoc, hK.1]
  · rw [R.w₁_assoc, hK.2, hg]
  · rw [← Category.assoc, hK.1]
  · rw [← Category.assoc, hK.2, hg']

/-- **The criterion (pages 20 and 22).** Under the covering homotopy extension
property, a diagonal `φ̄` homotopic to `φ` (on `X' ⊗ J`) and making both
triangles commute strictly exists if and only if there are homotopies
`k : φ i ⟶ g`, `h : p φ ⟶ g'` compatible with `i` and `p`. -/
theorem rectification_iff (hR : CoveringHomotopyExtension R p) {g : X ⟶ Y} {g' : X' ⟶ Y'}
    (φ : X' ⟶ Y) :
    (∃ (φbar : X' ⟶ Y) (K : R.P'.I ⟶ Y),
        i ≫ φbar = g ∧ φbar ≫ p = g' ∧ IsHomotopy R.P' K φ φbar) ↔
      ∃ (k : R.P.I ⟶ Y) (h : R.P'.I ⟶ Y'),
        IsHomotopy R.P k (i ≫ φ) g ∧ IsHomotopy R.P' h (φ ≫ p) g' ∧ k ≫ p = R.iJ ≫ h := by
  refine ⟨fun ⟨φbar, K, hg, hg', hK⟩ => ?_, fun ⟨k, h, hk, hh, hc⟩ => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := compatible_of_rectification R φ φbar hg hg' K hK
    exact ⟨_, _, h1, h2, h3⟩
  · obtain ⟨φbar, L, h1, h2, h3, -, -⟩ := rectification R hR φ k h hk hh hc
    exact ⟨φbar, L, h1, h2, h3⟩

/-- **Page 22, « in case `Y'` is final object we are evidently through ».**
When `Y'` is terminal, a homotopy `k : φ i ⟶ g` alone gives `φ̄`: the
compatibility, and the homotopy `h`, are automatic. -/
theorem rectification_of_isTerminal (hY' : IsTerminal Y') (hR : CoveringHomotopyExtension R p)
    {g : X ⟶ Y} {g' : X' ⟶ Y'} (φ : X' ⟶ Y) (k : R.P.I ⟶ Y)
    (hk : IsHomotopy R.P k (i ≫ φ) g) :
    ∃ φbar : X' ⟶ Y, i ≫ φbar = g ∧ φbar ≫ p = g' ∧
      ∃ L : R.P'.I ⟶ Y, IsHomotopy R.P' L φ φbar := by
  obtain ⟨φbar, L, h1, h2, h3, -, -⟩ :=
    rectification R hR φ k (hY'.from _) hk ⟨hY'.hom_ext _ _, hY'.hom_ext _ _⟩
      (hY'.hom_ext _ _)
  exact ⟨φbar, h1, h2, L, h3⟩

end

section ModelCategory

variable [ModelCategory C] {X X' Y Y' : C} {i : X ⟶ X'} (R : RelativeCylinder i)

/-- In a model category, the covering homotopy extension property holds for a
fibration `p` as soon as the corner map `X ⊗ J ⊔_X X' ⟶ X' ⊗ J` (the pushout
of `i₀ : X ⟶ X ⊗ J` and `i`) is a trivial cofibration: it is then mathlib's
lifting axiom `cm4a`. -/
theorem coveringHomotopyExtension_of_trivialCofibration (p : Y ⟶ Y') [Fibration p]
    [Cofibration (pushout.desc R.iJ R.P'.i₀ R.w₀)]
    [WeakEquivalence (pushout.desc R.iJ R.P'.i₀ R.w₀)] :
    CoveringHomotopyExtension R p := by
  intro a b c hb hc hbc
  have sq : CommSq (pushout.desc b a hb) (pushout.desc R.iJ R.P'.i₀ R.w₀) p c :=
    ⟨by ext <;> simp [hbc, hc]⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have := pushout.inr _ _ ≫= sq.fac_left
    rwa [pushout.inr_desc_assoc, pushout.inr_desc] at this
  · have := pushout.inl _ _ ≫= sq.fac_left
    rwa [pushout.inl_desc_assoc, pushout.inl_desc] at this

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
        IsHomotopy R.P k (i ≫ φ) g ∧ IsHomotopy R.P' h (φ ≫ p) g' ∧ k ≫ p = R.iJ ≫ h :=
  rectification_iff R (coveringHomotopyExtension_of_trivialCofibration R p) φ

end ModelCategory

end Grothendieck.Folder107
