module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Category.Cat

@[expose] public section

open CategoryTheory Opposite

namespace Grothendieck.Folder21.Stack

universe v' u'

variable {X : Type*} [TopologicalSpace X] (F : (Opens X)ᵒᵖ ⥤ Cat.{v', u'})

/-- The restriction functor `𝓕(V) ⥤ 𝓕(W)` along `W ≤ V`. -/
def res {V W : Opens X} (h : W ≤ V) : F.obj (op V) ⥤ F.obj (op W) :=
  (F.map (homOfLE h).op).toFunctor

theorem res_comp {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) :
    res F h₁ ⋙ res F h₂ = res F (h₂.trans h₁) := by
  simp only [res, ← Cat.Hom.comp_toFunctor, ← F.map_comp]
  rfl

theorem obj_res_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : F.obj (op U)) :
    (res F h₂).obj ((res F h₁).obj f) = (res F (h₂.trans h₁)).obj f :=
  Functor.congr_obj (res_comp F h₁ h₂) f

variable {F}

/-- Restriction `ρ_{S ≤ T}` on the presheaf `T ↦ Hom(f|T, g|T)` of a pair of objects over `V`. -/
def ρ {V T S : Opens X} {h : T ≤ V} (h₁ : S ≤ T) {f g : F.obj (op V)}
    (a : (res F h).obj f ⟶ (res F h).obj g) :
    (res F (h₁.trans h)).obj f ⟶ (res F (h₁.trans h)).obj g :=
  eqToHom (obj_res_res F h h₁ f).symm ≫ (res F h₁).map a ≫ eqToHom (obj_res_res F h h₁ g)

variable (F)

/-- `(P₃)` relative to `Y`: restriction is an equivalence. -/
def P3 (Y : Set X) : Prop :=
  ∀ ⦃V T : Opens X⦄ (h : T ≤ V), (T : Set X) = (V : Set X) \ Y → (res F h).IsEquivalence

/-- Faithfulness at `x` of `Pseudolim_W 𝓕(W) ⥤ Pseudolim_W 𝓕(W - W ∩ cl{x})`, unfolded:
two morphisms over a neighbourhood of `x` that agree off `cl{x}` agree near `x`. -/
def FaithfulAt (x : X) : Prop :=
  ∀ ⦃W T : Opens X⦄ (h : T ≤ W), x ∈ W → (T : Set X) = (W : Set X) \ closure {x} →
    ∀ ⦃f g : F.obj (op W)⦄ (a b : f ⟶ g), (res F h).map a = (res F h).map b →
      ∃ (W' : Opens X) (h' : W' ≤ W), x ∈ W' ∧ (res F h').map a = (res F h').map b

/-- Fullness at `x`, unfolded: a morphism off `cl{x}` agrees, near `x` and off `cl{x}`,
with a morphism defined near `x`. -/
def FullAt (x : X) : Prop :=
  ∀ ⦃W T : Opens X⦄ (h : T ≤ W), x ∈ W → (T : Set X) = (W : Set X) \ closure {x} →
    ∀ ⦃f g : F.obj (op W)⦄ (c : (res F h).obj f ⟶ (res F h).obj g),
      ∃ (W' : Opens X) (h' : W' ≤ W), x ∈ W' ∧
        ∃ (a : (res F h').obj f ⟶ (res F h').obj g) (S : Opens X) (h₁ : S ≤ W') (h₂ : S ≤ T),
          (S : Set X) = (W' : Set X) \ closure {x} ∧ ρ h₁ a = ρ h₂ c

/-- Essential surjectivity at `x`, unfolded: an object off `cl{x}` is, near `x` and off
`cl{x}`, isomorphic to the restriction of an object defined near `x`. -/
def EssSurjAt (x : X) : Prop :=
  ∀ ⦃W T : Opens X⦄ (_ : T ≤ W), x ∈ W → (T : Set X) = (W : Set X) \ closure {x} →
    ∀ e : F.obj (op T), ∃ (W' : Opens X) (_ : W' ≤ W), x ∈ W' ∧
      ∃ (f₀ : F.obj (op W')) (S : Opens X) (h₁ : S ≤ W') (h₂ : S ≤ T),
        (S : Set X) = (W' : Set X) \ closure {x} ∧ Nonempty ((res F h₁).obj f₀ ≅ (res F h₂).obj e)

/-- Descent of morphisms for covers by two opens (the Hom presheaves are sheaves for them). -/
structure IsBinaryPrestack : Prop where
  ext : ∀ ⦃A B T : Opens X⦄ (hA : A ≤ T) (hB : B ≤ T), (T : Set X) = (A : Set X) ∪ B →
    ∀ ⦃f g : F.obj (op T)⦄ (u v : f ⟶ g), (res F hA).map u = (res F hA).map v →
      (res F hB).map u = (res F hB).map v → u = v
  glue : ∀ ⦃A B D T : Opens X⦄ (hA : A ≤ T) (hB : B ≤ T) (hDA : D ≤ A) (hDB : D ≤ B),
    (T : Set X) = (A : Set X) ∪ B → (D : Set X) = (A : Set X) ∩ B →
    ∀ ⦃f g : F.obj (op T)⦄ (α : (res F hA).obj f ⟶ (res F hA).obj g)
      (β : (res F hB).obj f ⟶ (res F hB).obj g), ρ hDA α = ρ hDB β →
      ∃ u : f ⟶ g, (res F hA).map u = α ∧ (res F hB).map u = β

/-- A binary prestack in which objects also glue along covers by two opens. -/
structure IsBinaryStack : Prop extends IsBinaryPrestack F where
  glueObj : ∀ ⦃A B D T : Opens X⦄ (hA : A ≤ T) (hB : B ≤ T) (hDA : D ≤ A) (hDB : D ≤ B),
    (T : Set X) = (A : Set X) ∪ B → (D : Set X) = (A : Set X) ∩ B →
    ∀ (a : F.obj (op A)) (b : F.obj (op B)), Nonempty ((res F hDA).obj a ≅ (res F hDB).obj b) →
      ∃ t : F.obj (op T), Nonempty ((res F hA).obj t ≅ a) ∧ Nonempty ((res F hB).obj t ≅ b)

variable {F}

variable [NoetherianSpace X] [QuasiSober X]

/-- **Proposition 7, `(P₃)`**, for a stack (binary covers suffice): restriction to `V - Y` is
an equivalence for every open `V` iff the induced functor on germs at each `x ∈ Y` is one. -/
theorem proposition7_P3 (hF : IsBinaryStack F) {Y : Set X} (hY : IsClosed Y) :
    P3 F Y ↔ ∀ x ∈ Y, (FullAt F x ∧ FaithfulAt F x) ∧ EssSurjAt F x := by
  sorry

end Grothendieck.Folder21.Stack
