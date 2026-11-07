module

public import Mathlib

@[expose] public section


/-!
# Folder 137, pages 74–83: polynomial categories and `⊗`-pd-categories

The modernised reading `transcripts/137/137.modern.tex` (« Catégories polynomiales »,
pages 74 to 85) defines a *polynomial category* `𝐏`: a category with the same objects as
a wide subcategory `𝐏₁` of maps « of degree one », with `𝐏(X, Y) = ⊕ₙ 𝐏ₙ(X, Y)`, degrees
multiplying under composition (axiom e)), composition additive in the outer variable
only. Where `Y ↦ 𝐏ₙ(X, Y)` is representable on `𝐏₁` it defines `Γⁿ X` with a universal
`γₙ : X → Γⁿ X` of degree `n` (pp. 77–78), and the factorisation of `γ_p ∘ γ_q` through
`Γ^{pq} X` gives `α_{p,q} : Γ^{pq} → Γ^p Γ^q`, associative (the square of p. 80) and
unital for `Γ¹ = id`. Conversely (pp. 81–83), from `(Γ*, α)` on an additive `𝐏₁` one
sets `𝐏_p(X, Y) = Hom(Γ^p X, Y)` with `g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}`, and page 83 says
« Les deux notions sont donc équivalentes », without proof (finding
`137-polynomial-categories-pd-tensor-categories`).

What is formalised is the core of that equivalence, the part that carries the inverse
`𝐏_p(X, Y) = Hom(Γ^p X, Y)` and the composition rule, for any degree-one category `C`
(no additivity, no tensor product needed):

* `PDCategory C`: functors `Γⁿ : C ⥤ C`, natural `α_{p,q} : Γ^{pq} → Γ^p ∘ Γ^q`, an
  isomorphism `ε : Γ¹ ≅ id` (the page's `Γ¹ = id`), the unit conditions (**) and the
  associativity square of p. 80 — a comonad graded by the monoid `(ℕ, ·)`. Indices are
  carried with an equation `p * q = n`, so that no cast appears.
* `PolynomialCategory C`: sets `𝐏ₙ(X, Y)`, composition of degree `q * p`, identities of
  degree one, associativity, and an identification `ι : (X ⟶ Y) ≃ 𝐏₁(X, Y)` compatible
  with composition; `Representation`: objects `Γⁿ X` and `γₙ` representing `𝐏ₙ(X, -)`
  on `C`.
* `PDCategory.toPoly` (pp. 81–82): the composition `g ∘ Γ^q(f) ∘ α_{q,p}` is
  associative and unital, additive in `g` when `C` is preadditive (`toPoly_comp_add`),
  and `PDCategory.representation`: `𝐏ₙ(X, -)` is represented by `Γⁿ X`, `γₙ = id`.
* `Representation.toPD` (pp. 77–80): from a polynomial category with representable
  degrees, `Γⁿ` is a functor, `α_{p,q}` is natural, `Γ¹ ≅ id`, and (**) and the square
  of p. 80 hold.
* The two passages are inverse: `toPD_representation_Γ_map`, `toPD_representation_α`,
  `toPD_representation_ε` recover `Γ`, `α`, `ε` on the nose; `toPDToPolyIso` is an
  isomorphism of polynomial categories `𝐏_p(X, Y) ≃ Hom(Γ^p X, Y)`, `φ ↦ φ ∘ γ_p`,
  compatible with composition, identities and degree-one maps.

Not formalised: the products and the additivity of `𝐏` (axioms a)–c)), the
multidegree decompositions and homogeneity under scalars (d)), f), g) and the half
`𝟏 ≅ Γ^q(𝟏)` of (***), the tensor product, strictness, the exponential formula
`Γ*(X ⊕ Y) ≅ Γ*X ⊗ Γ*Y`, and the example of `k`-modules (Roby). Proving the statement
says only that it holds as formalised; whether it is in the literature is a separate
question.
-/

namespace Grothendieck.Folder137

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- A `⊗-pd`-category without its tensor product (pp. 80–82): functors `Γⁿ`, maps
`α_{p,q} : Γ^{pq} → Γ^p Γ^q` with the associativity square of p. 80, and the unit
conditions (**) for `Γ¹ ≅ id`. -/
structure PDCategory (C : Type u) [Category.{v} C] where
  Γ : ℕ → C ⥤ C
  α : ∀ p q n : ℕ, p * q = n → (Γ n ⟶ Γ q ⋙ Γ p)
  ε : Γ 1 ≅ 𝟭 C
  α_one_left : ∀ (q : ℕ) (X : C),
    (α 1 q q (one_mul q)).app X ≫ ε.hom.app ((Γ q).obj X) = 𝟙 _
  α_one_right : ∀ (q : ℕ) (X : C),
    (α q 1 q (mul_one q)).app X ≫ (Γ q).map (ε.hom.app X) = 𝟙 _
  α_assoc : ∀ (p q r m l n : ℕ) (hm : q * r = m) (hl : p * q = l) (h₁ : p * m = n)
    (h₂ : l * r = n) (X : C),
    (α p m n h₁).app X ≫ (Γ p).map ((α q r m hm).app X) =
      (α l r n h₂).app X ≫ (α p q l hl).app ((Γ r).obj X)

/-- The composition structure of a polynomial category (pp. 74–76): degrees multiply
under composition (axiom e)), with `C` as its subcategory of degree-one maps. The
composite of `f ∈ 𝐏_p(X, Y)` and `g ∈ 𝐏_q(Y, Z)` has degree `q * p`. -/
structure PolynomialCategory (C : Type u) [Category.{v} C] where
  Hom : ℕ → C → C → Type v
  comp : ∀ {p q n : ℕ} {X Y Z : C}, Hom p X Y → Hom q Y Z → q * p = n → Hom n X Z
  id : ∀ X : C, Hom 1 X X
  id_comp : ∀ {q : ℕ} {X Y : C} (g : Hom q X Y), comp (id X) g (mul_one q) = g
  comp_id : ∀ {p : ℕ} {X Y : C} (f : Hom p X Y), comp f (id Y) (one_mul p) = f
  assoc : ∀ {p q r m l n : ℕ} {W X Y Z : C} (f : Hom p W X) (g : Hom q X Y) (k : Hom r Y Z)
    (hm : r * q = m) (hl : q * p = l) (h₁ : m * p = n) (h₂ : r * l = n),
    comp (comp f g hl) k h₂ = comp f (comp g k hm) h₁
  ι : ∀ {X Y : C}, (X ⟶ Y) ≃ Hom 1 X Y
  ι_id : ∀ X : C, ι (𝟙 X) = id X
  ι_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), ι (f ≫ g) = comp (ι f) (ι g) (mul_one 1)

namespace PDCategory

variable (G : PDCategory C)

@[reassoc]
lemma α_one_left' (q : ℕ) (X : C) (h : 1 * q = q) :
    (G.α 1 q q h).app X ≫ G.ε.hom.app ((G.Γ q).obj X) = 𝟙 _ := G.α_one_left q X

@[reassoc]
lemma α_one_right' (q : ℕ) (X : C) (h : q * 1 = q) :
    (G.α q 1 q h).app X ≫ (G.Γ q).map (G.ε.hom.app X) = 𝟙 _ := G.α_one_right q X

@[reassoc]
lemma α_assoc' (p q r m l n : ℕ) (hm : q * r = m) (hl : p * q = l) (h₁ : p * m = n)
    (h₂ : l * r = n) (X : C) :
    (G.α p m n h₁).app X ≫ (G.Γ p).map ((G.α q r m hm).app X) =
      (G.α l r n h₂).app X ≫ (G.α p q l hl).app ((G.Γ r).obj X) :=
  G.α_assoc p q r m l n hm hl h₁ h₂ X

/-- The polynomial category of a `⊗-pd`-category (pp. 81–82): `𝐏_p(X, Y) = Hom(Γ^p X, Y)`,
`g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}`, identity `ε : Γ¹ X → X`. -/
def toPoly : PolynomialCategory C where
  Hom p X Y := (G.Γ p).obj X ⟶ Y
  comp {p q n X Y Z} f g h := (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g
  id X := G.ε.hom.app X
  id_comp {q X Y} g := by rw [G.α_one_right'_assoc]
  comp_id {p X Y} f := by
    have := G.ε.hom.naturality f
    simp only [Functor.id_map] at this
    rw [this, G.α_one_left'_assoc]
  assoc {p q r m l n W X Y Z} f g k hm hl h₁ h₂ := by
    simp only [Functor.map_comp, Category.assoc]
    have nat := (G.α r q m hm).naturality f
    simp only [Functor.comp_map] at nat
    rw [reassoc_of% nat, ← G.α_assoc'_assoc r q p l m n hl hm h₂ h₁]
  ι {X Y} :=
    { toFun := fun f => G.ε.hom.app X ≫ f
      invFun := fun g => G.ε.inv.app X ≫ g
      left_inv := fun f => by simp
      right_inv := fun g => by simp }
  ι_id X := by simp
  ι_comp {X Y Z} f g := by
    simp only [Equiv.coe_fn_mk, Functor.map_comp, Category.assoc]
    have n1 := G.ε.hom.naturality f
    have n2 := G.ε.hom.naturality (G.ε.hom.app X)
    simp only [Functor.id_map] at n1 n2
    rw [reassoc_of% n1, reassoc_of% n2, G.α_one_left'_assoc]

end PDCategory


namespace PolynomialCategory

variable (P : PolynomialCategory C)

/-- Associativity with the inner degree `m` prescribed. -/
lemma assoc' {p q r m l n : ℕ} {W X Y Z : C} (f : P.Hom p W X) (g : P.Hom q X Y)
    (k : P.Hom r Y Z) (hm : r * q = m) {hl : q * p = l} {h₂ : r * l = n} :
    P.comp (P.comp f g hl) k h₂ = P.comp f (P.comp g k hm) (by subst hl h₂ hm; ring) :=
  P.assoc f g k hm hl _ h₂

/-- Associativity, right to left, with the inner degree `l` prescribed. -/
lemma assoc'' {p q r m l n : ℕ} {W X Y Z : C} (f : P.Hom p W X) (g : P.Hom q X Y)
    (k : P.Hom r Y Z) (hl : q * p = l) {hm : r * q = m} {h₁ : m * p = n} :
    P.comp f (P.comp g k hm) h₁ = P.comp (P.comp f g hl) k (by subst hm h₁ hl; ring) :=
  (P.assoc f g k hm hl h₁ _).symm

lemma comp_id' {p : ℕ} {X Y : C} (f : P.Hom p X Y) (h : 1 * p = p) :
    P.comp f (P.id Y) h = f := P.comp_id f

lemma id_comp' {q : ℕ} {X Y : C} (g : P.Hom q X Y) (h : q * 1 = q) :
    P.comp (P.id X) g h = g := P.id_comp g

lemma ι_comp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : 1 * 1 = 1) :
    P.comp (P.ι f) (P.ι g) h = P.ι (f ≫ g) := (P.ι_comp f g).symm

/-- Representability of `P_n(X, -)` on the degree-one maps: an object `Γⁿ X` and a
universal map `γₙ : X → Γⁿ X` of degree `n` (pp. 77–78). -/
structure Representation (P : PolynomialCategory C) where
  obj : ℕ → C → C
  γ : ∀ (n : ℕ) (X : C), P.Hom n X (obj n X)
  bij : ∀ (n : ℕ) (X Y : C),
    Function.Bijective (fun φ : obj n X ⟶ Y => P.comp (γ n X) (P.ι φ) (one_mul n))

namespace Representation

variable {P} (R : P.Representation)

/-- `Hom(Γⁿ X, Y) ≃ P_n(X, Y)`, `φ ↦ φ ∘ γₙ`. -/
noncomputable def rep (n : ℕ) (X Y : C) : (R.obj n X ⟶ Y) ≃ P.Hom n X Y :=
  Equiv.ofBijective _ (R.bij n X Y)

lemma rep_apply {n : ℕ} {X Y : C} (φ : R.obj n X ⟶ Y) :
    R.rep n X Y φ = P.comp (R.γ n X) (P.ι φ) (one_mul n) := rfl

lemma rep_comp {n : ℕ} {X Y Z : C} (φ : R.obj n X ⟶ Y) (ψ : Y ⟶ Z) :
    R.rep n X Z (φ ≫ ψ) = P.comp (R.rep n X Y φ) (P.ι ψ) (one_mul n) := by
  simp only [rep_apply, P.ι_comp]
  rw [P.assoc' _ _ _ (mul_one 1)]

lemma rep_id (n : ℕ) (X : C) : R.rep n X _ (𝟙 _) = R.γ n X := by
  rw [rep_apply, P.ι_id, P.comp_id]

lemma rep_symm_apply {n : ℕ} {X Y : C} (a : P.Hom n X Y) :
    R.rep n X Y ((R.rep n X Y).symm a) = a := Equiv.apply_symm_apply _ a

lemma hom_ext {n : ℕ} {X Y : C} {φ ψ : R.obj n X ⟶ Y}
    (h : R.rep n X Y φ = R.rep n X Y ψ) : φ = ψ := (R.rep n X Y).injective h

/-- `Γⁿ` on degree-one maps: `Γⁿ(f)` corresponds to `γₙ ∘ f`. -/
noncomputable def map (n : ℕ) {X X' : C} (f : X ⟶ X') : R.obj n X ⟶ R.obj n X' :=
  (R.rep n X _).symm (P.comp (P.ι f) (R.γ n X') (mul_one n))

lemma rep_map (n : ℕ) {X X' : C} (f : X ⟶ X') :
    R.rep n X _ (R.map n f) = P.comp (P.ι f) (R.γ n X') (mul_one n) := rep_symm_apply _ _

/-- The functor `Γⁿ : P₁ → P₁`. -/
noncomputable def functor (n : ℕ) : C ⥤ C where
  obj := R.obj n
  map f := R.map n f
  map_id X := by
    apply R.hom_ext
    rw [rep_map, rep_id, P.ι_id, P.id_comp]
  map_comp {X Y Z} f g := by
    apply R.hom_ext
    rw [rep_map, rep_comp, rep_map, P.assoc' _ _ _ (one_mul n), ← rep_apply, rep_map,
      P.assoc'' _ _ _ (mul_one 1), P.ι_comp' f g]

/-- `α_{p,q} : Γ^{pq} X → Γ^p Γ^q X` corresponds to `γ_p ∘ γ_q` (p. 80). -/
noncomputable def αApp (p q n : ℕ) (h : p * q = n) (X : C) :
    R.obj n X ⟶ R.obj p (R.obj q X) :=
  (R.rep n X _).symm (P.comp (R.γ q X) (R.γ p (R.obj q X)) h)

lemma rep_αApp (p q n : ℕ) (h : p * q = n) (X : C) :
    R.rep n X _ (R.αApp p q n h X) = P.comp (R.γ q X) (R.γ p (R.obj q X)) h :=
  rep_symm_apply _ _

/-- The counit `Γ¹ X → X` corresponds to the identity of `X`. -/
noncomputable def εHom (X : C) : R.obj 1 X ⟶ X := (R.rep 1 X X).symm (P.id X)

lemma rep_εHom (X : C) : R.rep 1 X X (R.εHom X) = P.id X := rep_symm_apply _ _

lemma map_αApp (p q n : ℕ) (h : p * q = n) {X X' : C} (f : X ⟶ X') :
    R.map n f ≫ R.αApp p q n h X' = R.αApp p q n h X ≫ R.map p (R.map q f) := by
  apply R.hom_ext
  rw [rep_comp, rep_map, P.assoc' _ _ _ (one_mul n), ← rep_apply, rep_αApp,
    rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul p), ← rep_apply, rep_map,
    P.assoc'' _ _ _ (one_mul q), ← rep_apply, rep_map, P.assoc' _ _ _ h]

lemma εHom_inv (X : C) : R.εHom X ≫ P.ι.symm (R.γ 1 X) = 𝟙 _ := by
  apply R.hom_ext
  rw [rep_comp, rep_εHom, Equiv.apply_symm_apply, P.id_comp, rep_id]

lemma inv_εHom (X : C) : P.ι.symm (R.γ 1 X) ≫ R.εHom X = 𝟙 _ := by
  apply P.ι.injective
  rw [P.ι_comp, Equiv.apply_symm_apply, ← rep_apply, rep_εHom, P.ι_id]

lemma map_εHom {X X' : C} (f : X ⟶ X') : R.map 1 f ≫ R.εHom X' = R.εHom X ≫ f := by
  apply R.hom_ext
  rw [rep_comp, rep_map, P.assoc' _ _ _ (mul_one 1), ← rep_apply, rep_εHom,
    P.comp_id' _ (mul_one 1), rep_comp, rep_εHom, P.id_comp]

lemma αApp_one_left (q : ℕ) (X : C) (h : 1 * q = q) :
    R.αApp 1 q q h X ≫ R.εHom (R.obj q X) = 𝟙 _ := by
  apply R.hom_ext
  rw [rep_comp, rep_αApp, P.assoc' _ _ _ (mul_one 1), ← rep_apply, rep_εHom,
    P.comp_id' _ (one_mul q), rep_id]

lemma αApp_one_right (q : ℕ) (X : C) (h : q * 1 = q) :
    R.αApp q 1 q h X ≫ R.map q (R.εHom X) = 𝟙 _ := by
  apply R.hom_ext
  rw [rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul q), ← rep_apply, rep_map,
    P.assoc'' _ _ _ (mul_one 1), ← rep_apply, rep_εHom, P.id_comp, rep_id]

lemma αApp_assoc (p q r m l n : ℕ) (hm : q * r = m) (hl : p * q = l) (h₁ : p * m = n)
    (h₂ : l * r = n) (X : C) :
    R.αApp p m n h₁ X ≫ R.map p (R.αApp q r m hm X) =
      R.αApp l r n h₂ X ≫ R.αApp p q l hl (R.obj r X) := by
  apply R.hom_ext
  rw [rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul p), ← rep_apply, rep_map,
    P.assoc'' _ _ _ (one_mul m), ← rep_apply, rep_αApp, rep_comp, rep_αApp,
    P.assoc' _ _ _ (one_mul l), ← rep_apply, rep_αApp, P.assoc' _ _ _ hl]

/-- `α_{p,q}` as a natural transformation `Γ^{pq} → Γ^p ∘ Γ^q`. -/
noncomputable def α (p q n : ℕ) (h : p * q = n) : R.functor n ⟶ R.functor q ⋙ R.functor p where
  app X := R.αApp p q n h X
  naturality {_ _} f := R.map_αApp p q n h f

/-- The counit `Γ¹ ≅ id`: `Γ¹ X` represents `P₁(X, -) = Hom(X, -)`. -/
noncomputable def ε : R.functor 1 ≅ 𝟭 C :=
  NatIso.ofComponents
    (fun X =>
      { hom := R.εHom X
        inv := P.ι.symm (R.γ 1 X)
        hom_inv_id := R.εHom_inv X
        inv_hom_id := R.inv_εHom X })
    (fun f => R.map_εHom f)

/-- The `⊗-pd`-structure (without `⊗`) of a polynomial category with representable
degrees: the functors `Γⁿ`, the maps `α_{p,q}` and the unit conditions (pp. 77–80). -/
noncomputable def toPD : PDCategory C where
  Γ := R.functor
  α := R.α
  ε := R.ε
  α_one_left q X := R.αApp_one_left q X _
  α_one_right q X := R.αApp_one_right q X _
  α_assoc p q r m l n hm hl h₁ h₂ X := R.αApp_assoc p q r m l n hm hl h₁ h₂ X

end Representation

end PolynomialCategory

/-- The trivial model: every `Γⁿ` the identity, every `α_{p,q}` the identity; then
`𝐏ₙ(X, Y) = Hom(X, Y)` for every `n`. It shows the axioms are consistent. -/
def PDCategory.trivial (C : Type u) [Category.{v} C] : PDCategory C where
  Γ _ := 𝟭 C
  α _ _ _ _ := 𝟙 (𝟭 C)
  ε := Iso.refl _
  α_one_left _ _ := by simp
  α_one_right _ _ := by simp
  α_assoc _ _ _ _ _ _ _ _ _ _ _ := by simp

/-! ### The two passages are inverse to each other -/

/-- An isomorphism of polynomial categories on the same degree-one category:
bijections of each `P_n(X, Y)` compatible with composition, identities and the
degree-one maps. -/
structure PolynomialCategory.Iso (P Q : PolynomialCategory C) where
  e : ∀ (n : ℕ) (X Y : C), P.Hom n X Y ≃ Q.Hom n X Y
  map_comp : ∀ {p q n : ℕ} {X Y Z : C} (f : P.Hom p X Y) (g : P.Hom q Y Z) (h : q * p = n),
    e n X Z (P.comp f g h) = Q.comp (e p X Y f) (e q Y Z g) h
  map_id : ∀ X : C, e 1 X X (P.id X) = Q.id X
  map_ι : ∀ {X Y : C} (f : X ⟶ Y), e 1 X Y (P.ι f) = Q.ι f

namespace PDCategory

variable (G : PDCategory C)

lemma toPoly_comp {p q n : ℕ} {X Y Z : C} (f : (G.Γ p).obj X ⟶ Y) (g : (G.Γ q).obj Y ⟶ Z)
    (h : q * p = n) :
    G.toPoly.comp (X := X) f g h = (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g := rfl

/-- Composition `g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}` is additive in the outer variable `g`
(p. 82), when the degree-one category is additive. -/
lemma toPoly_comp_add [Preadditive C] {p q n : ℕ} {X Y Z : C} (f : (G.Γ p).obj X ⟶ Y)
    (g g' : (G.Γ q).obj Y ⟶ Z) (h : q * p = n) :
    G.toPoly.comp (X := X) f (g + g') h =
      (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g + (G.α q p n h).app X ≫ (G.Γ q).map f ≫ g' := by
  simp only [toPoly_comp, Preadditive.comp_add]
  rfl

/-- In the polynomial category of a `⊗-pd`-category, `P_n(X, -)` is represented on the
degree-one maps by `Γⁿ X`, with universal map `γₙ = id_{Γⁿ X}` (p. 82: `𝐏_p(X, Y) =
Hom(Γ^p X, Y)`). -/
def representation : G.toPoly.Representation where
  obj n X := (G.Γ n).obj X
  γ n X := 𝟙 ((G.Γ n).obj X)
  bij n X Y := by
    have e : ∀ φ : (G.Γ n).obj X ⟶ Y,
        G.toPoly.comp (X := X) (𝟙 _) (G.toPoly.ι φ) (one_mul n) = φ := fun φ => by
      change (G.α 1 n n _).app X ≫ (G.Γ 1).map (𝟙 _) ≫ G.ε.hom.app _ ≫ φ = φ
      simp [G.α_one_left'_assoc]
    exact ⟨fun a b hab => (e a).symm.trans (hab.trans (e b)), fun b => ⟨b, e b⟩⟩

lemma representation_rep {n : ℕ} {X Y : C} (φ : (G.Γ n).obj X ⟶ Y) :
    G.representation.rep n X Y φ = φ := by
  change (G.α 1 n n _).app X ≫ (G.Γ 1).map (𝟙 _) ≫ G.ε.hom.app _ ≫ φ = φ
  simp [G.α_one_left'_assoc]

/-- Round trip `⊗-pd → polynomial → ⊗-pd`: the functors `Γⁿ` are recovered. -/
theorem toPD_representation_Γ_map (n : ℕ) {X X' : C} (f : X ⟶ X') :
    (G.representation.toPD.Γ n).map f = (G.Γ n).map f := by
  apply G.representation.hom_ext
  change G.representation.rep n X _ (G.representation.map n f) =
    G.representation.rep n X _ ((G.Γ n).map f)
  rw [G.representation.rep_map, representation_rep]
  change (G.α n 1 n _).app X ≫ (G.Γ n).map (G.ε.hom.app X ≫ f) ≫ 𝟙 _ = _
  rw [Category.comp_id, Functor.map_comp, G.α_one_right'_assoc]

/-- Round trip: the maps `α_{p,q}` are recovered. -/
theorem toPD_representation_α (p q n : ℕ) (h : p * q = n) (X : C) :
    (G.representation.toPD.α p q n h).app X = (G.α p q n h).app X := by
  apply G.representation.hom_ext
  change G.representation.rep n X _ (G.representation.αApp p q n h X) =
    G.representation.rep n X _ ((G.α p q n h).app X)
  rw [G.representation.rep_αApp, representation_rep]
  change (G.α p q n h).app X ≫ (G.Γ p).map (𝟙 _) ≫ 𝟙 _ = _
  simp

/-- Round trip: the counit `Γ¹ ≅ id` is recovered. -/
theorem toPD_representation_ε (X : C) :
    G.representation.toPD.ε.hom.app X = G.ε.hom.app X := by
  apply G.representation.hom_ext
  change G.representation.rep 1 X X (G.representation.εHom X) =
    G.representation.rep 1 X X (G.ε.hom.app X)
  rw [G.representation.rep_εHom, representation_rep]
  rfl

end PDCategory

namespace PolynomialCategory.Representation

variable {P : PolynomialCategory C} (R : P.Representation)

lemma toPD_toPoly_comp {p q n : ℕ} {X Y Z : C} (f : R.obj p X ⟶ Y) (g : R.obj q Y ⟶ Z)
    (h : q * p = n) :
    R.rep n X Z (R.toPD.toPoly.comp (X := X) f g h) = P.comp (R.rep p X Y f) (R.rep q Y Z g) h := by
  change R.rep n X Z (R.αApp q p n h X ≫ R.map q f ≫ g) = _
  rw [← Category.assoc, rep_comp, rep_comp, rep_αApp, P.assoc' _ _ _ (one_mul q),
    ← rep_apply, rep_map, P.assoc'' _ _ _ (one_mul p), ← rep_apply,
    P.assoc' _ _ _ (one_mul q), ← rep_apply]

/-- Round trip `polynomial → ⊗-pd → polynomial`: the polynomial category built from
`(Γ, α, ε)` by `𝐏_p(X, Y) = Hom(Γ^p X, Y)` and `g ∘ f = g ∘ Γ^q(f) ∘ α_{q,p}` is
isomorphic to the one we started from, by `φ ↦ φ ∘ γ_p`. -/
noncomputable def toPDToPolyIso : R.toPD.toPoly.Iso P where
  e n X Y := R.rep n X Y
  map_comp f g h := R.toPD_toPoly_comp f g h
  map_id X := R.rep_εHom X
  map_ι {X Y} f := by
    change R.rep 1 X Y (R.εHom X ≫ f) = _
    rw [rep_comp, rep_εHom, P.id_comp]

end PolynomialCategory.Representation

end Grothendieck.Folder137

/-!
# Folder 137, pages 39–56: `𝒫` and the universal complex `ℂ^•`

The reading (« Classes de suites exactes et propriété universelle », pages 48 to 56) takes
for `𝒫` the chain complexes of finitely generated free `k`-modules, zero outside finitely
many degrees (degrees `≥ 0`, as the discs `ℂⁱ`, `i ≥ 0`, require), for `Σ` the sequences
`0 → L' → L → L'' → 0` exact in each degree, and for `ℂ^•` the cochain complex of discs
`ℂⁱ = (k → k)` in degrees `i + 1`, `i`. The theorem of p. 50 says that `F ↦ F(ℂ^•)`, from the
`k`-linear functors `𝒫 → ℬ` carrying `Σ` to left exact sequences to the cochain complexes of
`ℬ`, is fully faithful, and an equivalence if `ℬ` has kernels (finding
`137-perfect-complexes-universal-sigma-exact`).

What is formalised, over any commutative ring `k`:

* the discs `disc k n`, the differential `dmap k n : ℂⁿ → ℂⁿ⁺¹`, and Proposition 1 of p. 40 in
  `𝒫`: `End(ℂⁿ) = k · id` (`disc_endo`), `Hom(ℂⁿ, ℂⁿ⁺¹) = k · dⁿ` (`disc_succ`),
  `Hom(ℂⁿ, ℂʲ) = 0` otherwise (`disc_zero`), so `ℂ^•` is a cochain complex of `𝒫` (`univ`);
* the category `Perf k` (`𝒫`), the class `IsSigma`, and, for every `L`, the `Σ`-sequence
  `0 → L → I(L) → L[1] → 0` (`isSigma_cone`), `I(L)` the cone of the identity, which is a
  finite sum of discs: `∑ p_{n,b} ≫ e_{n,b} = 𝟙` over a basis of each `Lₙ` (`total`);
* **the theorem of p. 50, a), first half**: for any `k`-linear category `ℬ`, without kernels,
  `ρ : F ↦ F(ℂ^•)` is fully faithful on the `k`-linear `Σ`-left exact functors
  (`ρFullyFaithful`). A morphism `F(ℂ^•) → G(ℂ^•)` commutes with all maps between discs
  (`discNat`, which is where Proposition 1 enters), hence extends to every finite sum of discs
  (`phi_nat`), and to `L` through the kernel `G(L) = ker(G(I(L)) → G(L[1]))` (`extend`).

Not formalised: the essential surjectivity (the second half of a), with `ℬ` having kernels,
through `σ(C^•)(L) = Hom^•_k(L^•, C^•)`), part b) on `Σ`-exact functors and `Σ`-resolutions,
Propositions 2 and 3 of pp. 42–44, and the cosimplicial version of pp. 45–46. Proving the
statement says only that it holds as formalised; whether it is in the literature is a
separate question.
-/

namespace Grothendieck.Folder137.Perfect

open CategoryTheory Limits

universe u

noncomputable section

variable (k : Type u) [CommRing k]

/-- The support of the disc `ℂⁿ`: `k` in degrees `n` and `n + 1`, `0` elsewhere. -/
def discS (n m : ℕ) : Submodule k k := if m = n ∨ m = n + 1 then ⊤ else ⊥

lemma mem_discS_of_eq (n m : ℕ) (h : m = n ∨ m = n + 1) (x : k) : x ∈ discS k n m := by
  simp [discS, h]

lemma eq_zero_of_mem_discS {n m : ℕ} (h : ¬ (m = n ∨ m = n + 1)) {x : k}
    (hx : x ∈ discS k n m) : x = 0 := by
  simpa [discS, h] using hx

/-- The differential of the disc, the identity of `k` from degree `n + 1` to degree `n`. -/
def discD (n m : ℕ) : ModuleCat.of k (discS k n (m + 1)) ⟶ ModuleCat.of k (discS k n m) :=
  ModuleCat.ofHom (LinearMap.codRestrict (discS k n m)
    ((if m = n then LinearMap.id else 0) ∘ₗ (discS k n (m + 1)).subtype) (fun x => by
      by_cases h : m = n
      · exact mem_discS_of_eq k n m (Or.inl h) _
      · simp [h]))

@[simp]
lemma discD_apply (n m : ℕ) (x : ModuleCat.of k (discS k n (m + 1))) :
    Subtype.val ((discD k n m).hom x) = if m = n then Subtype.val x else 0 := by
  by_cases h : m = n <;> simp [discD, h]

/-- The disc `ℂⁿ` (p. 39): the chain complex `k → k`, identity, in degrees `n + 1`, `n`. -/
noncomputable abbrev disc (n : ℕ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun m => ModuleCat.of k (discS k n m)) (discD k n) (fun m => by
    ext x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, discD_apply, discD_apply]
    split_ifs <;> first | rfl | omega)

/-- The value in `k` of an element of a component of a disc. -/
def dv {n m : ℕ} (x : (disc k n).X m) : k := (show discS k n m from x).1

@[simp]
lemma disc_d_apply (n m : ℕ) (x : (disc k n).X (m + 1)) :
    dv k (((disc k n).d (m + 1) m).hom x) = if m = n then dv k x else 0 := by
  rw [show (disc k n).d (m + 1) m = discD k n m by simp [disc]]
  exact discD_apply k n m x

@[simp]
lemma dv_discD (n m : ℕ) (x : (disc k n).X (m + 1)) :
    dv k ((discD k n m).hom x) = if m = n then dv k x else 0 := discD_apply k n m x

@[simp] lemma dv_smul {n m : ℕ} (c : k) (x : (disc k n).X m) : dv k (c • x) = c * dv k x := rfl
@[simp] lemma dv_add {n m : ℕ} (x y : (disc k n).X m) : dv k (x + y) = dv k x + dv k y := rfl
@[simp] lemma dv_zero {n m : ℕ} : dv k (0 : (disc k n).X m) = 0 := rfl
@[simp] lemma dv_neg {n m : ℕ} (x : (disc k n).X m) : dv k (-x) = - dv k x := rfl

lemma dv_eq_zero {n m : ℕ} (h : ¬ (m = n ∨ m = n + 1)) (x : (disc k n).X m) : dv k x = 0 :=
  eq_zero_of_mem_discS k h x.2

@[ext]
lemma disc_ext {n m : ℕ} {x y : (disc k n).X m} (h : dv k x = dv k y) : x = y :=
  Subtype.ext h

variable {k}

/-- A chain map of `ℕ`-graded chain complexes from its components. -/
def mkHom {X Y : ChainComplex (ModuleCat.{u} k) ℕ} (f : ∀ m, X.X m ⟶ Y.X m)
    (comm : ∀ m, f (m + 1) ≫ Y.d (m + 1) m = X.d (m + 1) m ≫ f m) : X ⟶ Y where
  f := f
  comm' := by
    rintro i j (rfl : j + 1 = i)
    exact comm j

/-- A map into the disc `ℂⁿ` from linear forms `ψₘ` on the components (`ψₙ₊₁ = ψₙ ∘ d`). -/
def toDisc {X : ChainComplex (ModuleCat.{u} k) ℕ} (n : ℕ) (ψ : ∀ m, X.X m →ₗ[k] k)
    (hs : ∀ m x, ¬ (m = n ∨ m = n + 1) → ψ m x = 0)
    (hc : ∀ m x, ψ m ((X.d (m + 1) m).hom x) = if m = n then ψ (m + 1) x else 0) :
    X ⟶ disc k n :=
  mkHom (fun m => ModuleCat.ofHom (LinearMap.codRestrict (discS k n m) (ψ m) (fun x => by
      by_cases h : m = n ∨ m = n + 1
      · exact mem_discS_of_eq k n m h _
      · rw [hs m x h]; exact zero_mem _)))
    (fun m => by
      ext x
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, disc_d_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply]
      exact (hc m x).symm)

@[simp]
lemma toDisc_apply {X : ChainComplex (ModuleCat.{u} k) ℕ} (n : ℕ) (ψ : ∀ m, X.X m →ₗ[k] k) hs hc
    (m : ℕ) (x : X.X m) : dv k (((toDisc n ψ hs hc).f m).hom x) = ψ m x := rfl

/-- A map out of the disc `ℂⁿ` from a family `vₘ ∈ Xₘ` with `d v_{n+1} = vₙ`:
`c ↦ c • vₘ` in degree `m`. -/
def fromDisc {X : ChainComplex (ModuleCat.{u} k) ℕ} (n : ℕ) (v : ∀ m, X.X m)
    (hv : (X.d (n + 1) n).hom (v (n + 1)) = v n) : disc k n ⟶ X :=
  mkHom (fun m => ModuleCat.ofHom ((discS k n m).subtype.smulRight (v m)))
    (fun m => by
      ext x
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
      change (X.d (m + 1) m).hom (dv k x • v (m + 1)) =
        dv k (((disc k n).d (m + 1) m).hom x) • v m
      rw [disc_d_apply, map_smul]
      by_cases h : m = n
      · subst h; rw [ite_eq_left rfl, hv]
      · rw [ite_eq_right h, zero_smul]
        by_cases h' : m + 1 = n
        · subst h'
          rw [← hv]
          have := congr($(X.d_comp_d (m + 1 + 1) (m + 1) m).hom (v (m + 1 + 1)))
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
            LinearMap.zero_apply] at this
          rw [this, smul_zero]
        · rw [dv_eq_zero k (by omega) x, zero_smul])

@[simp]
lemma fromDisc_apply {X : ChainComplex (ModuleCat.{u} k) ℕ} (n : ℕ) (v : ∀ m, X.X m) hv
    (m : ℕ) (x : (disc k n).X m) : ((fromDisc n v hv).f m).hom x = dv k x • v m := rfl

variable (k) in
/-- The generator `1` of the disc `ℂⁿ`, in degree `n + 1`. -/
def one (n : ℕ) : (disc k n).X (n + 1) := ⟨1, mem_discS_of_eq k n (n + 1) (Or.inr rfl) 1⟩

@[simp] lemma dv_one (n : ℕ) : dv k (one k n) = 1 := rfl

/-- A map out of `ℂⁿ` is determined by the image of the generator. -/
lemma disc_hom_ext {n : ℕ} {X : ChainComplex (ModuleCat.{u} k) ℕ} {f g : disc k n ⟶ X}
    (h : (f.f (n + 1)).hom (one k n) = (g.f (n + 1)).hom (one k n)) : f = g := by
  have top : ∀ x : (disc k n).X (n + 1), (f.f (n + 1)).hom x = (g.f (n + 1)).hom x := by
    intro x
    have hx : x = dv k x • one k n := disc_ext k (by simp [dv, one])
    rw [hx, map_smul, map_smul, h]
  ext m x
  by_cases h1 : m = n + 1
  · subst h1; exact top x
  by_cases h2 : m = n
  · subst h2
    let y : (disc k m).X (m + 1) := dv k x • one k m
    have hy : ((disc k m).d (m + 1) m).hom y = x := disc_ext k (by
      rw [disc_d_apply, ite_eq_left rfl]
      exact mul_one _)
    rw [← hy]
    have cf := congr($(f.comm (m + 1) m).hom y)
    have cg := congr($(g.comm (m + 1) m).hom y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at cf cg
    rw [← cf, ← cg, top]
  · have : x = 0 := disc_ext k (eq_zero_of_mem_discS k (by omega)
      (show (x : k) ∈ discS k n m from x.2))
    rw [this, map_zero, map_zero]

variable (k) in
/-- The generator of `ℂⁿ⁺¹` in degree `n + 1`, as a family. -/
def dmapV (n m : ℕ) : (disc k (n + 1)).X m :=
  if h : m = n + 1 then ⟨1, mem_discS_of_eq k (n + 1) m (Or.inl h) 1⟩ else 0

variable (k) in
/-- The differential `dⁿ : ℂⁿ → ℂⁿ⁺¹` of the universal complex: the identity of `k` in
degree `n + 1`, where `ℂⁿ` has its top and `ℂⁿ⁺¹` its bottom. -/
def dmap (n : ℕ) : disc k n ⟶ disc k (n + 1) :=
  fromDisc n (dmapV k n)
    (disc_ext k (by
      rw [disc_d_apply, ite_eq_right (by omega), dmapV, dite_eq_right (by omega)]
      rfl))

lemma dmap_apply (n m : ℕ) (x : (disc k n).X m) :
    ((dmap k n).f m).hom x = dv k x • dmapV k n m := rfl

lemma dv_dmap (n m : ℕ) (x : (disc k n).X m) :
    dv k (((dmap k n).f m).hom x) = if m = n + 1 then dv k x else 0 := by
  rw [dmap_apply, dmapV]
  split_ifs with h
  · subst h; exact mul_one _
  · exact mul_zero _

lemma smul_f_apply {X Y : ChainComplex (ModuleCat.{u} k) ℕ} (c : k) (f : X ⟶ Y) (m : ℕ)
    (x : X.X m) : ((c • f).f m).hom x = c • (f.f m).hom x := rfl

/-- Proposition 1 (p. 40), the endomorphisms of a disc: `End(ℂⁿ) = k · id`. -/
lemma disc_endo {n : ℕ} (f : disc k n ⟶ disc k n) :
    f = dv k ((f.f (n + 1)).hom (one k n)) • 𝟙 _ := by
  refine disc_hom_ext (disc_ext k ?_)
  rw [smul_f_apply]
  change _ = _ * dv k (one k n)
  rw [dv_one, mul_one]

/-- Proposition 1 (p. 40): `Hom(ℂⁿ, ℂⁿ⁺¹) = k · dⁿ`. -/
lemma disc_succ {n : ℕ} (f : disc k n ⟶ disc k (n + 1)) :
    f = dv k ((f.f (n + 1)).hom (one k n)) • dmap k n := by
  refine disc_hom_ext (disc_ext k ?_)
  rw [smul_f_apply, dv_smul, dv_dmap, ite_eq_left rfl, dv_one, mul_one]

/-- Proposition 1 (p. 40): `Hom(ℂⁿ, ℂʲ) = 0` for `j ∉ {n, n + 1}`. -/
lemma disc_zero {n j : ℕ} (f : disc k n ⟶ disc k j) (h₁ : j ≠ n) (h₂ : j ≠ n + 1) : f = 0 := by
  refine disc_hom_ext (disc_ext k ?_)
  rw [dv_eq_zero k (by omega)]
  rfl

lemma dmap_comp_dmap (n : ℕ) : dmap k n ≫ dmap k (n + 1) = 0 :=
  disc_zero _ (by omega) (by omega)

/-! ### The cone of the identity `I(L)` and the sequence `0 → L → I(L) → L[1] → 0` -/

section Cone

variable (L : ChainComplex (ModuleCat.{u} k) ℕ)

/-- The shifted components: `Lp 0 = 0`, `Lp (m + 1) = Lₘ`. -/
def Lp : ℕ → ModuleCat.{u} k
  | 0 => ModuleCat.of k PUnit.{u + 1}
  | m + 1 => L.X m

/-- The differential `Lₘ → Lₘ₋₁`, as a map `Lₘ → Lp m`. -/
def dL : ∀ m, L.X m →ₗ[k] Lp L m
  | 0 => 0
  | m + 1 => (L.d (m + 1) m).hom

lemma dL_d (m : ℕ) (x : L.X (m + 1)) : dL L m ((L.d (m + 1) m).hom x) = 0 := by
  cases m with
  | zero => rfl
  | succ m =>
    change (L.d (m + 1) m).hom ((L.d (m + 1 + 1) (m + 1)).hom x) = 0
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, L.d_comp_d]
    rfl

/-- The differential of the shift `L[1]` (sign `−1`). -/
def dSh : ∀ m, Lp L (m + 1) ⟶ Lp L m
  | 0 => 0
  | m + 1 => -L.d (m + 1) m

/-- The shift `L[1]`: `L[1]ₘ = Lₘ₋₁`, differential `−d`. -/
abbrev shift : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (Lp L) (dSh L) (fun m => by
    cases m with
    | zero => exact comp_zero
    | succ m =>
      change (-L.d (m + 1 + 1) (m + 1)) ≫ (-L.d (m + 1) m) = 0
      rw [Preadditive.neg_comp_neg, L.d_comp_d])

/-- The differential of the cone `I(L)`: `(a, b) ↦ (b, 0)`. -/
def dI (m : ℕ) : ModuleCat.of k (L.X (m + 1) × Lp L (m + 1)) ⟶ ModuleCat.of k (L.X m × Lp L m) :=
  ModuleCat.ofHom (LinearMap.inl k (L.X m) (Lp L m) ∘ₗ LinearMap.snd k (L.X (m + 1)) (L.X m))

@[simp] lemma dI_apply (m : ℕ) (x : L.X (m + 1) × Lp L (m + 1)) :
    (dI L m).hom x = ((x.2 : L.X m), 0) := rfl

/-- The cone of the identity `I(L)`: `I(L)ₘ = Lₘ ⊕ Lₘ₋₁`, `d(a, b) = (b, 0)`; it is a finite
sum of discs (`decI`). -/
abbrev cone : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun m => ModuleCat.of k (L.X m × Lp L m)) (dI L) (fun m => by
    ext x <;> rfl)

lemma cone_d_apply (m : ℕ) (x : (cone L).X (m + 1)) :
    ((cone L).d (m + 1) m).hom x = (((show L.X (m + 1) × Lp L (m + 1) from x).2 : L.X m), 0) := by
  rw [show (cone L).d (m + 1) m = dI L m by simp]
  rfl

lemma shift_d_apply (m : ℕ) (x : L.X (m + 1)) :
    ((shift L).d (m + 1 + 1) (m + 1)).hom x = -(L.d (m + 1) m).hom x := by
  rw [show (shift L).d (m + 1 + 1) (m + 1) = -L.d (m + 1) m by simp; rfl]
  rfl

lemma shift_d_zero (x : (shift L).X 1) : ((shift L).d 1 0).hom x = 0 := by
  rw [show (shift L).d 1 0 = 0 by simp; rfl]
  rfl

/-- `ι : L → I(L)`, `a ↦ (a, da)`. -/
def coneι : L ⟶ cone L :=
  mkHom (fun m => ModuleCat.ofHom (LinearMap.prod LinearMap.id (dL L m))) (fun m => by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [cone_d_apply]
    change ((dL L (m + 1) x : L.X m), (0 : Lp L m)) = ((L.d (m + 1) m).hom x,
      dL L m ((L.d (m + 1) m).hom x))
    rw [dL_d]
    rfl)

/-- `π : I(L) → L[1]`, `(a, b) ↦ b − da`. -/
def coneπ : cone L ⟶ shift L :=
  mkHom (fun m => ModuleCat.ofHom (LinearMap.snd k _ _ - dL L m ∘ₗ LinearMap.fst k _ _))
    (fun m => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      obtain ⟨a, b⟩ := x
      cases m with
      | zero =>
        change ((shift L).d 1 0).hom _ = (0 : Lp L 0) - dL L 0 (show L.X 0 from b)
        rw [shift_d_zero]
        rfl
      | succ m =>
        rw [show (cone L).d (m + 1 + 1) (m + 1) = dI L (m + 1) by simp]
        change ((shift L).d (m + 1 + 1) (m + 1)).hom ((show L.X (m + 1) from b) -
            (L.d (m + 1 + 1) (m + 1)).hom a) = (0 : L.X m) - (L.d (m + 1) m).hom b
        rw [shift_d_apply, map_sub, ← LinearMap.comp_apply (L.d (m + 1) m).hom,
          ← ModuleCat.hom_comp, L.d_comp_d]
        simp only [ModuleCat.hom_zero, LinearMap.zero_apply, sub_zero, zero_sub]
        rfl)

@[simp] lemma coneι_apply (m : ℕ) (x : L.X m) : ((coneι L).f m).hom x = (x, dL L m x) := rfl
@[simp] lemma coneπ_apply (m : ℕ) (x : L.X m × Lp L m) :
    ((coneπ L).f m).hom x = x.2 - dL L m x.1 := rfl

lemma coneι_comp_coneπ : coneι L ≫ coneπ L = 0 := by
  ext m : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun x => sub_self _)

variable {L} {M : ChainComplex (ModuleCat.{u} k) ℕ}

/-- `g` on the shifted components. -/
def gp (g : L ⟶ M) : ∀ m, Lp L m →ₗ[k] Lp M m
  | 0 => 0
  | m + 1 => (g.f m).hom

/-- `I(g) : I(L) → I(M)`, `(a, b) ↦ (g a, g b)`. -/
def coneMap (g : L ⟶ M) : cone L ⟶ cone M :=
  mkHom (fun m => ModuleCat.ofHom (LinearMap.prodMap (g.f m).hom (gp g m))) (fun m => by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    obtain ⟨a, b⟩ := x
    rw [show (cone L).d (m + 1) m = dI L m by simp, show (cone M).d (m + 1) m = dI M m by simp]
    change (((g.f m).hom b : M.X m), (0 : Lp M m)) = ((g.f m).hom b, gp g m 0)
    rw [map_zero])

lemma coneι_comp_coneMap (g : L ⟶ M) : coneι L ≫ coneMap g = g ≫ coneι M := by
  ext m : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change ((g.f m).hom x, gp g m (dL L m x)) = ((g.f m).hom x, dL M m ((g.f m).hom x))
  congr 1
  cases m with
  | zero => rfl
  | succ m =>
    change (g.f m).hom ((L.d (m + 1) m).hom x) = (M.d (m + 1) m).hom ((g.f (m + 1)).hom x)
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← g.comm (m + 1) m]
    rfl

end Cone

/-! ### The category `𝒫` and the class `Σ` (p. 48) -/

variable (k) in
/-- `𝒫` (p. 48): chain complexes of finitely generated free `k`-modules, zero in large
degrees (and in negative degrees, being indexed by `ℕ`). -/
def perfect : ObjectProperty (ChainComplex (ModuleCat.{u} k) ℕ) := fun L =>
  (∀ m, Module.Free k (L.X m) ∧ Module.Finite k (L.X m)) ∧
    ∃ N, ∀ m, N < m → Subsingleton (L.X m)

variable (k) in
/-- The category `𝒫` of p. 48. -/
abbrev Perf := (perfect k).FullSubcategory

lemma free_finite_top_bot (S : Submodule k k) (h : S = ⊤ ∨ S = ⊥) :
    Module.Free k S ∧ Module.Finite k S := by
  rcases h with rfl | rfl
  · exact ⟨Module.Free.of_equiv Submodule.topEquiv.symm,
      Module.Finite.equiv Submodule.topEquiv.symm⟩
  · exact ⟨inferInstance, inferInstance⟩

lemma disc_perfect (n : ℕ) : perfect k (disc k n) := by
  refine ⟨fun m => free_finite_top_bot (discS k n m) ?_, ⟨n + 1, fun m hm => ?_⟩⟩
  · unfold discS; split_ifs <;> simp
  · change Subsingleton (discS k n m)
    unfold discS
    rw [ite_eq_right (by omega)]
    infer_instance

lemma Lp_perfect {L : ChainComplex (ModuleCat.{u} k) ℕ} (hL : perfect k L) (m : ℕ) :
    Module.Free k (Lp L m) ∧ Module.Finite k (Lp L m) := by
  cases m with
  | zero => exact ⟨inferInstanceAs (Module.Free k PUnit.{u + 1}),
      inferInstanceAs (Module.Finite k PUnit.{u + 1})⟩
  | succ m => exact hL.1 m

lemma cone_perfect {L : ChainComplex (ModuleCat.{u} k) ℕ} (hL : perfect k L) :
    perfect k (cone L) := by
  obtain ⟨N, hN⟩ := hL.2
  refine ⟨fun m => ?_, ⟨N + 1, fun m hm => ?_⟩⟩
  · obtain ⟨_, _⟩ := hL.1 m
    obtain ⟨_, _⟩ := Lp_perfect hL m
    exact ⟨inferInstanceAs (Module.Free k (L.X m × Lp L m)),
      inferInstanceAs (Module.Finite k (L.X m × Lp L m))⟩
  · have := hN m (by omega)
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have := hN m (by omega)
    exact inferInstanceAs (Subsingleton (L.X (m + 1) × L.X m))

lemma shift_perfect {L : ChainComplex (ModuleCat.{u} k) ℕ} (hL : perfect k L) :
    perfect k (shift L) := by
  obtain ⟨N, hN⟩ := hL.2
  refine ⟨fun m => Lp_perfect hL m, ⟨N + 1, fun m hm => ?_⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact hN m (by omega)

variable (k) in
/-- The disc `ℂⁿ` as an object of `𝒫`. -/
abbrev D (n : ℕ) : Perf k := ⟨disc k n, disc_perfect n⟩

variable (k) in
/-- The differential `dⁿ : ℂⁿ → ℂⁿ⁺¹` in `𝒫`. -/
def dP (n : ℕ) : D k n ⟶ D k (n + 1) := ObjectProperty.homMk (dmap k n)

variable (k) in
/-- The universal cochain complex `ℂ⁰ → ℂ¹ → ⋯` of `𝒫` (p. 39). -/
def univ : CochainComplex (Perf k) ℕ :=
  CochainComplex.of (D k) (dP k) (fun n => by
    ext : 1
    exact dmap_comp_dmap n)

/-- The class `Σ` of p. 48: sequences `0 → L' → L → L'' → 0` exact in each degree. -/
structure IsSigma {L' L L'' : Perf k} (f : L' ⟶ L) (g : L ⟶ L'') : Prop where
  injective : ∀ m, Function.Injective (f.hom.f m).hom
  surjective : ∀ m, Function.Surjective (g.hom.f m).hom
  exact : ∀ m x, (g.hom.f m).hom x = 0 ↔ ∃ y, (f.hom.f m).hom y = x

/-- `I(L)` as an object of `𝒫`. -/
abbrev coneP (L : Perf k) : Perf k := ⟨cone L.obj, cone_perfect L.property⟩

/-- `L[1]` as an object of `𝒫`. -/
abbrev shiftP (L : Perf k) : Perf k := ⟨shift L.obj, shift_perfect L.property⟩

/-- `ι : L → I(L)` in `𝒫`. -/
def ιP (L : Perf k) : L ⟶ coneP L := ObjectProperty.homMk (coneι L.obj)

/-- `π : I(L) → L[1]` in `𝒫`. -/
def πP (L : Perf k) : coneP L ⟶ shiftP L := ObjectProperty.homMk (coneπ L.obj)

/-- `I(g)` in `𝒫`. -/
def coneMapP {L M : Perf k} (g : L ⟶ M) : coneP L ⟶ coneP M := ObjectProperty.homMk (coneMap g.hom)

lemma ιP_comp_coneMapP {L M : Perf k} (g : L ⟶ M) : ιP L ≫ coneMapP g = g ≫ ιP M := by
  ext : 1
  exact coneι_comp_coneMap g.hom

lemma ιP_comp_πP (L : Perf k) : ιP L ≫ πP L = 0 := by
  ext : 1
  exact coneι_comp_coneπ L.obj

/-- Every object of `𝒫` is the kernel of a `Σ`-sequence `0 → L → I(L) → L[1] → 0` (p. 52). -/
lemma isSigma_cone (L : Perf k) : IsSigma (ιP L) (πP L) where
  injective m x y h := congr_arg Prod.fst h
  surjective m y := ⟨((0 : L.obj.X m), (show Lp L.obj m from y)), by
    change (show Lp L.obj m from y) - dL L.obj m 0 = y
    rw [map_zero, sub_zero]⟩
  exact m x := by
    obtain ⟨a, b⟩ := x
    change b - dL L.obj m a = 0 ↔ ∃ y, (y, dL L.obj m y) = (a, b)
    constructor
    · exact fun h => ⟨a, by rw [sub_eq_zero.mp h]⟩
    · rintro ⟨y, hy⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy
      exact sub_self _

/-! ### `I(L)` is a finite sum of discs -/

section Dec

variable (L : Perf k)

/-- The index set of the chosen basis of `Lₙ`. -/
def Bi (n : ℕ) : Type u :=
  @Module.Free.ChooseBasisIndex k (L.obj.X n) _ _ _ (L.property.1 n).1

instance (n : ℕ) : Fintype (Bi L n) :=
  @Module.Free.ChooseBasisIndex.fintype k (L.obj.X n) _ _ _ (L.property.1 n).1 (L.property.1 n).2

/-- The chosen basis of `Lₙ`. -/
def bas (n : ℕ) : Module.Basis (Bi L n) k (L.obj.X n) :=
  @Module.Free.chooseBasis k (L.obj.X n) _ _ _ (L.property.1 n).1

/-- `b` seen in `Lp (n + 1) = Lₙ`. -/
def basS (n : ℕ) (b : Bi L n) : Lp L.obj (n + 1) := bas L n b

/-- `b*` seen on `Lp (n + 1) = Lₙ`. -/
def coordS (n : ℕ) (b : Bi L n) : Lp L.obj (n + 1) →ₗ[k] k := (bas L n).coord b

/-- The element `(0, b)` of `I(L)ₙ₊₁` (and `(b, 0)` of `I(L)ₙ`), image of the generator of
`ℂⁿ` under `e_{n,b}`. -/
def vv (n : ℕ) (b : Bi L n) (m : ℕ) : (cone L.obj).X m :=
  (Pi.single (M := fun m => (L.obj.X m : Type u)) n (bas L n b) m,
    Pi.single (M := fun m => (Lp L.obj m : Type u)) (n + 1) (basS L n b) m)

/-- The linear forms `(a, c) ↦ b*(a)` in degree `n`, `b*(c)` in degree `n + 1`, defining
`p_{n,b} : I(L) → ℂⁿ`. -/
def ψ (n : ℕ) (b : Bi L n) (m : ℕ) : (cone L.obj).X m →ₗ[k] k :=
  (Pi.single (M := fun m => (L.obj.X m →ₗ[k] k)) n ((bas L n).coord b) m) ∘ₗ
      LinearMap.fst k _ _ +
    (Pi.single (M := fun m => (Lp L.obj m →ₗ[k] k)) (n + 1) (coordS L n b) m) ∘ₗ
      LinearMap.snd k _ _

lemma ψ_apply (n : ℕ) (b : Bi L n) (m : ℕ) (x : (cone L.obj).X m) :
    ψ L n b m x = Pi.single (M := fun m => (L.obj.X m →ₗ[k] k)) n ((bas L n).coord b) m x.1 +
      Pi.single (M := fun m => (Lp L.obj m →ₗ[k] k)) (n + 1) (coordS L n b) m x.2 := rfl

lemma ψ_ne (n : ℕ) (b : Bi L n) (m : ℕ) (h : ¬ (m = n ∨ m = n + 1)) (x : (cone L.obj).X m) :
    ψ L n b m x = 0 := by
  rw [ψ_apply, Pi.single_eq_of_ne (show m ≠ n by omega),
    Pi.single_eq_of_ne (show m ≠ n + 1 by omega)]
  simp

lemma ψ_self (n : ℕ) (b : Bi L n) (x : (cone L.obj).X n) :
    ψ L n b n x = (bas L n).coord b x.1 := by
  rw [ψ_apply, Pi.single_eq_same, Pi.single_eq_of_ne (show n ≠ n + 1 by omega)]
  simp

lemma ψ_succ (n : ℕ) (b : Bi L n) (x : (cone L.obj).X (n + 1)) :
    ψ L n b (n + 1) x = coordS L n b x.2 := by
  rw [ψ_apply, Pi.single_eq_same, Pi.single_eq_of_ne (show n + 1 ≠ n by omega)]
  simp

lemma ψ_d (n : ℕ) (b : Bi L n) (m : ℕ) (x : (cone L.obj).X (m + 1)) :
    ψ L n b m (((cone L.obj).d (m + 1) m).hom x) =
      if m = n then ψ L n b (m + 1) x else 0 := by
  rw [show (cone L.obj).d (m + 1) m = dI L.obj m by simp]
  by_cases h : m = n
  · subst h
    rw [ite_eq_left rfl, ψ_succ, ψ_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (show m ≠ m + 1 by omega)]
    simp only [LinearMap.zero_apply, add_zero]
    rfl
  · rw [ite_eq_right h, ψ_apply, Pi.single_eq_of_ne h]
    simp only [LinearMap.zero_apply, zero_add]
    by_cases h' : m = n + 1
    · subst h'
      rw [Pi.single_eq_same]
      exact map_zero _
    · rw [Pi.single_eq_of_ne h']
      rfl

lemma vv_d (n : ℕ) (b : Bi L n) :
    ((cone L.obj).d (n + 1) n).hom (vv L n b (n + 1)) = vv L n b n := by
  rw [cone_d_apply]
  refine Prod.ext ?_ ?_
  · change Pi.single (M := fun m => (Lp L.obj m : Type u)) (n + 1) (basS L n b) (n + 1) =
      Pi.single (M := fun m => (L.obj.X m : Type u)) n (bas L n b) n
    rw [Pi.single_eq_same, Pi.single_eq_same]
    rfl
  · exact (Pi.single_eq_of_ne (M := fun m => (Lp L.obj m : Type u))
      (show n ≠ n + 1 by omega) _).symm

/-- `e_{n,b} : ℂⁿ → I(L)`. -/
def eDec (n : ℕ) (b : Bi L n) : D k n ⟶ coneP L :=
  ObjectProperty.homMk (fromDisc n (vv L n b) (vv_d L n b))

/-- `p_{n,b} : I(L) → ℂⁿ`. -/
def pDec (n : ℕ) (b : Bi L n) : coneP L ⟶ D k n :=
  ObjectProperty.homMk (toDisc n (ψ L n b) (fun m x h => ψ_ne L n b m h x)
    (fun m x => ψ_d L n b m x))

/-- A bound beyond which `L` vanishes. -/
def bound : ℕ := (L.property : perfect k L.obj).2.choose

lemma bound_spec (m : ℕ) (h : bound L < m) : Subsingleton (L.obj.X m) :=
  (L.property : perfect k L.obj).2.choose_spec m h

lemma vv_fst_self (n : ℕ) (b : Bi L n) : (vv L n b n).1 = bas L n b := Pi.single_eq_same _ _

lemma vv_fst_ne (n : ℕ) (b : Bi L n) (m : ℕ) (h : m ≠ n) : (vv L n b m).1 = 0 :=
  Pi.single_eq_of_ne (M := fun m => (L.obj.X m : Type u)) h _

lemma vv_snd_succ (n : ℕ) (b : Bi L n) : (vv L n b (n + 1)).2 = basS L n b :=
  Pi.single_eq_same (M := fun m => (Lp L.obj m : Type u)) _ _

lemma vv_snd_ne (n : ℕ) (b : Bi L n) (m : ℕ) (h : m ≠ n + 1) : (vv L n b m).2 = 0 :=
  Pi.single_eq_of_ne (M := fun m => (Lp L.obj m : Type u)) h _

lemma total_apply (m : ℕ) (x : (cone L.obj).X m) :
    ∑ n ∈ Finset.range (bound L + 1), ∑ b, ψ L n b m x • vv L n b m = x := by
  apply Prod.ext
  · rw [Prod.fst_sum]
    simp_rw [Prod.fst_sum, Prod.smul_fst]
    rw [Finset.sum_eq_single m]
    · calc ∑ b, ψ L m b m x • (vv L m b m).1 = ∑ b, (bas L m).repr x.1 b • bas L m b :=
            Finset.sum_congr rfl fun b _ => by rw [ψ_self, vv_fst_self]; rfl
        _ = x.1 := (bas L m).sum_repr x.1
    · intro n _ hn
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [vv_fst_ne L n b m (Ne.symm hn), smul_zero]
    · intro hm
      exact @Subsingleton.elim _ (bound_spec L m (by simp at hm; omega)) _ _
  · rw [Prod.snd_sum]
    simp_rw [Prod.snd_sum, Prod.smul_snd]
    cases m with
    | zero =>
      refine (Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun b _ => ?_).trans
        (Subsingleton.elim (α := PUnit.{u + 1}) _ _)
      rw [vv_snd_ne L n b 0 (by omega), smul_zero]
    | succ m =>
      rw [Finset.sum_eq_single m]
      · exact (Finset.sum_congr rfl fun b _ => by rw [ψ_succ, vv_snd_succ]; rfl).trans
          ((bas L m).sum_repr x.2)
      · intro n _ hn
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [vv_snd_ne L n b (m + 1) (by omega), smul_zero]
      · intro hm
        exact @Subsingleton.elim (L.obj.X m) (bound_spec L m (by simp at hm; omega)) _ _

lemma hom_sum {X Y : Perf k} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := (perfect k).ι.map_sum f s

lemma f_sum {X Y : ChainComplex (ModuleCat.{u} k) ℕ} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y))
    (m : ℕ) : (∑ i ∈ s, f i).f m = ∑ i ∈ s, (f i).f m :=
  (HomologicalComplex.eval _ _ m).map_sum f s

/-- The decomposition `∑ p_{n,b} ≫ e_{n,b} = 𝟙` of `I(L)` through discs. -/
lemma total : ∑ n ∈ Finset.range (bound L + 1), ∑ b, pDec L n b ≫ eDec L n b =
    𝟙 (coneP L) := by
  ext m : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  simp only [hom_sum, f_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Eq.trans ?_ (total_apply L m x)
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun b _ => rfl

end Dec

/-! ### The theorem of p. 50, a): `F ↦ F(ℂ^•)` is fully faithful -/

section Theorem

universe v₂ u₂

variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear k B]

/-- `F` transforms the sequences of `Σ` into left exact sequences (p. 50): `F(L')` is a
kernel of `F(L) → F(L'')`. -/
def SigmaLeftExact (F : Perf k ⥤ B) : Prop :=
  ∀ ⦃L' L L'' : Perf k⦄ (f : L' ⟶ L) (g : L ⟶ L''), IsSigma f g →
    ∃ w : F.map f ≫ F.map g = 0, Nonempty (IsLimit (KernelFork.ofι (F.map f) w))

variable (k B) in
/-- The `k`-linear functors `𝒫 → ℬ` that are `Σ`-left exact. -/
def lexFun : ObjectProperty (Perf k ⥤ B) := fun F =>
  F.Additive ∧ F.Linear k ∧ SigmaLeftExact F

variable (k B) in
/-- The category `Fonct_{k, Σ-sex}(𝒫, ℬ)` of p. 55. -/
abbrev Lex := (lexFun k B).FullSubcategory

instance (F : Lex k B) : F.obj.Additive := F.property.1
instance (F : Lex k B) : F.obj.Linear k := F.property.2.1

lemma lex_mono (F : Lex k B) (L : Perf k) : Mono (F.obj.map (ιP L)) := by
  obtain ⟨w, ⟨hl⟩⟩ := F.property.2.2 _ _ (isSigma_cone L)
  exact Fork.IsLimit.mono hl

/-- The kernel property of `F(L) → F(I(L)) → F(L[1])`. -/
def lexLimit (F : Lex k B) (L : Perf k) :
    IsLimit (KernelFork.ofι (F.obj.map (ιP L)) (by
      rw [← F.obj.map_comp, ιP_comp_πP, F.obj.map_zero])) :=
  (F.property.2.2 _ _ (isSigma_cone L)).choose_spec.some

variable (k B) in
/-- `ρ(F) = F(ℂ^•)`, the cochain complex `F(ℂ⁰) → F(ℂ¹) → ⋯` of `ℬ`. -/
def ρ : Lex k B ⥤ CochainComplex B ℕ where
  obj F := CochainComplex.of (fun n => F.obj.obj (D k n)) (fun n => F.obj.map (dP k n))
    (fun n => by rw [← F.obj.map_comp, show dP k n ≫ dP k (n + 1) = 0 by
      ext : 1; exact dmap_comp_dmap n, F.obj.map_zero])
  map {F G} η :=
    { f := fun n => η.hom.app (D k n)
      comm' := by
        rintro i j (rfl : i + 1 = j)
        simp only [CochainComplex.of_d]
        exact (η.hom.naturality (dP k i)).symm }

lemma ρ_d (F : Lex k B) (n : ℕ) : ((ρ k B).obj F).d n (n + 1) = F.obj.map (dP k n) := by
  simp [ρ]

variable {F G : Lex k B} (φ : (ρ k B).obj F ⟶ (ρ k B).obj G)

/-- The components `φₙ : F(ℂⁿ) → G(ℂⁿ)`. -/
def φf (n : ℕ) : F.obj.obj (D k n) ⟶ G.obj.obj (D k n) := φ.f n

lemma φ_comm (n : ℕ) : F.obj.map (dP k n) ≫ φf φ (n + 1) = φf φ n ≫ G.obj.map (dP k n) := by
  have := φ.comm n (n + 1)
  rw [ρ_d, ρ_d] at this
  exact this.symm

lemma smul_hom {X Y : Perf k} (c : k) (f : X ⟶ Y) : (c • f).hom = c • f.hom := rfl

/-- Proposition 1 (p. 40) at work: a morphism of complexes `F(ℂ^•) → G(ℂ^•)` commutes with
every map between discs, since these are `c • id`, `c • dⁿ` or `0`. -/
lemma discNat {i j : ℕ} (g : D k i ⟶ D k j) : F.obj.map g ≫ φf φ j = φf φ i ≫ G.obj.map g := by
  by_cases h₁ : j = i
  · subst h₁
    have : g = dv k ((g.hom.f (j + 1)).hom (one k j)) • 𝟙 _ := by
      ext : 1; exact disc_endo g.hom
    rw [this, Functor.map_smul, Functor.map_smul, F.obj.map_id, G.obj.map_id,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  by_cases h₂ : j = i + 1
  · subst h₂
    have : g = dv k ((g.hom.f (i + 1)).hom (one k i)) • dP k i := by
      ext : 1; exact disc_succ g.hom
    rw [this, Functor.map_smul, Functor.map_smul, Linear.smul_comp, Linear.comp_smul, φ_comm]
  · have : g = 0 := by ext : 1; exact disc_zero g.hom h₁ h₂
    rw [this, F.obj.map_zero, G.obj.map_zero, zero_comp, comp_zero]

/-- `Φ` on `I(L)`, through its decomposition into discs: `∑ F(p_{n,b}) ≫ φₙ ≫ G(e_{n,b})`. -/
def PhiI (L : Perf k) : F.obj.obj (coneP L) ⟶ G.obj.obj (coneP L) :=
  ∑ n ∈ Finset.range (bound L + 1), ∑ b, F.obj.map (pDec L n b) ≫ φf φ n ≫ G.obj.map (eDec L n b)

lemma PhiI_def (L : Perf k) : PhiI φ L = ∑ n ∈ Finset.range (bound L + 1), ∑ b,
    F.obj.map (pDec L n b) ≫ φf φ n ≫ G.obj.map (eDec L n b) := rfl

lemma phi_disc {n : ℕ} {M : Perf k} (g : D k n ⟶ coneP M) :
    F.obj.map g ≫ PhiI φ M = φf φ n ≫ G.obj.map g := by
  simp only [PhiI, Preadditive.comp_sum]
  conv_rhs => rw [← Category.comp_id g, ← total M]
  simp only [Preadditive.comp_sum, Functor.map_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Functor.map_comp_assoc, reassoc_of% (discNat φ (g ≫ pDec M m c))]
  simp only [Functor.map_comp, Category.assoc]

lemma phi_nat {L M : Perf k} (h : coneP L ⟶ coneP M) :
    F.obj.map h ≫ PhiI φ M = PhiI φ L ≫ G.obj.map h := by
  conv_lhs => rw [← Category.id_comp h, ← total L]
  rw [PhiI_def φ L]
  simp only [Preadditive.sum_comp, Functor.map_sum, Category.assoc]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, ← Functor.map_comp, phi_disc,
    Functor.map_comp]

lemma app_cone (η : F ⟶ G) (L : Perf k) : η.hom.app (coneP L) = PhiI ((ρ k B).map η) L := by
  conv_lhs => rw [← Category.id_comp (η.hom.app _), ← F.obj.map_id, ← total L]
  simp only [Functor.map_sum, Preadditive.sum_comp, PhiI]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Functor.map_comp, Category.assoc, η.hom.naturality]
  rfl

instance : (ρ k B).Faithful where
  map_injective {F G} η₁ η₂ h := by
    ext L : 3
    have := lex_mono G L
    rw [← cancel_mono (G.obj.map (ιP L)), ← η₁.hom.naturality, ← η₂.hom.naturality,
      app_cone, app_cone, h]

/-- The extension of `φ` to `L`: the lift through the kernel `G(L) → G(I(L))` of
`F(L) → F(I(L)) → G(I(L))`. -/
def extend (L : Perf k) : F.obj.obj L ⟶ G.obj.obj L :=
  (KernelFork.IsLimit.lift' (lexLimit G L) (F.obj.map (ιP L) ≫ PhiI φ L) (by
    have := lex_mono G (shiftP L)
    rw [← cancel_mono (G.obj.map (ιP (shiftP L))), Category.assoc, Category.assoc, zero_comp,
      ← G.obj.map_comp, ← phi_nat, ← F.obj.map_comp_assoc, ← Category.assoc, ιP_comp_πP,
      zero_comp, F.obj.map_zero, zero_comp])).1

lemma extend_spec (L : Perf k) : extend φ L ≫ G.obj.map (ιP L) = F.obj.map (ιP L) ≫ PhiI φ L :=
  (KernelFork.IsLimit.lift' (lexLimit G L) _ _).2

/-- The natural transformation `F ⟶ G` extending `φ`. -/
def extNat : F ⟶ G :=
  ObjectProperty.homMk
    { app := extend φ
      naturality := fun L M g => by
        have := lex_mono G M
        rw [← cancel_mono (G.obj.map (ιP M)), Category.assoc, extend_spec, ← F.obj.map_comp_assoc,
          ← ιP_comp_coneMapP, F.obj.map_comp, Category.assoc, phi_nat, ← Category.assoc,
          ← extend_spec, Category.assoc, ← G.obj.map_comp, ιP_comp_coneMapP, G.obj.map_comp]
        simp only [Category.assoc] }

instance : (ρ k B).Full where
  map_surjective {F G} φ := ⟨extNat φ, by
    ext n : 1
    have := lex_mono G (D k n)
    change extend φ (D k n) = φf φ n
    rw [← cancel_mono (G.obj.map (ιP (D k n))), extend_spec, phi_disc]⟩

variable (k B) in
/-- **Theorem (p. 50, a), first half).** `F ↦ F(ℂ^•)` is fully faithful from the `k`-linear
`Σ`-left exact functors `𝒫 → ℬ` to the cochain complexes of `ℬ`, for any `k`-linear
category `ℬ` — no kernels needed. -/
def ρFullyFaithful : (ρ k B).FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _

end Theorem

end

end Grothendieck.Folder137.Perfect

/-!
# Folder 137, page 50, a), second half: `σ(C^•)` and the essential surjectivity

For a cochain complex `C^•` of a `k`-linear category `ℬ`, page 50 builds the inverse
`σ(C^•)(L) = Hom^•_k(L^•, C^•)`. Here it is built through what it represents: for an object
`T` of `ℬ`, `Hom(T, C^•)` is a cochain complex of `k`-modules `M`, and the maps `T → σ(C^•)(L)`
are the cycles `Φ_T(L) ⊆ ∏ₙ Lₙ ⊗ Mⁿ`, the families `zₙ` with `(1 ⊗ d) zₙ = (d ⊗ 1) zₙ₊₁` (the
chain maps `L^∨ → M`, `Lₙ ⊗ Mⁿ = Hom(Lₙ^∨, Mⁿ)` as `Lₙ` is free of finite rank).

* `Phi`, `PhiMap`, `PhiPre`: `Φ_T(L)`, functorial in `L` and `T`; it is left exact on `Σ`
  (`PhiMap_injective`, `PhiMap_exact`): the sequences of `Σ` split in each degree, `L''ₙ`
  being free, so `- ⊗ Mⁿ` keeps them exact.
* `Rep C L X`: `X` represents `T ↦ Φ_T(L)`. The disc `ℂⁿ` is represented by `Cⁿ`
  (`discRep`); `I(L)`, a finite sum of discs, by a finite biproduct of the `Cⁿ` (`coneRep`,
  which uses that the `e_{n,b}`, `p_{n,b}` of `total` are orthogonal); `L` by the kernel of the
  map `σ(I(L)) → σ(I(L[1]))` that represents `I(L) → L[1] → I(L[1])` (`kerRep`).
* `σFun k C : 𝒫 ⥤ ℬ`, `k`-linear and `Σ`-left exact (`σLex`), with `ρ(σ(C^•)) ≅ C^•`
  (`σIso`).
  With `ρFullyFaithful`, `ρ` is an equivalence (`ρEquivalence`).

The hypotheses on `ℬ`: `k`-linear, with kernels **and finite biproducts** (`ℬ` additive).
Kernels are what page 50 asks; the biproducts are needed as well, since a `k`-linear functor
sends `ℂⁿ ⊕ ℂⁿ` to a biproduct `F(ℂⁿ) ⊕ F(ℂⁿ)`: in the full subcategory `{0, k}` of the
`k`-vector spaces (`k` a field), which has kernels but not `k ⊕ k`, the complex `k` in degree
`0` is not of the form `F(ℂ^•)` (this necessity is an argument of the edition, not
formalised).
-/

namespace Grothendieck.Folder137.Perfect

open CategoryTheory Limits TensorProduct

universe u v₂ u₂

noncomputable section

variable {k : Type u} [CommRing k]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B] [Linear k B]

/-! ### The cycles `Φ_T(L)` -/

section Phi

lemma lTensor_rTensor_apply {A A' N N' : Type*} [AddCommGroup A] [AddCommGroup A']
    [AddCommGroup N] [AddCommGroup N'] [Module k A] [Module k A'] [Module k N] [Module k N']
    (f : A →ₗ[k] A') (g : N →ₗ[k] N') (t : A ⊗[k] N) :
    g.lTensor A' (f.rTensor N t) = f.rTensor N' (g.lTensor A t) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

variable (C : CochainComplex B ℕ)

/-- `Φ_T(L)`: the families `zₙ ∈ Lₙ ⊗ Hom(T, Cⁿ)` with `(1 ⊗ d) zₙ = (d ⊗ 1) zₙ₊₁`, the maps
`T → σ(C^•)(L)`. -/
def Phi (T : B) (L : ChainComplex (ModuleCat.{u} k) ℕ) :
    Submodule k (∀ n, L.X n ⊗[k] (T ⟶ C.X n)) where
  carrier := {z | ∀ n, (Linear.rightComp k T (C.d n (n + 1))).lTensor (L.X n) (z n) =
      (L.d (n + 1) n).hom.rTensor (T ⟶ C.X (n + 1)) (z (n + 1))}
  add_mem' {a b} ha hb n := by
    simp only [Pi.add_apply, map_add]
    exact congrArg₂ (· + ·) (ha n) (hb n)
  zero_mem' n := by simp
  smul_mem' c a ha n := by
    simp only [Pi.smul_apply, map_smul]
    exact congrArg (c • ·) (ha n)

variable {C}

@[ext]
lemma Phi_ext {T : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} {z z' : Phi C T L}
    (h : ∀ n, z.1 n = z'.1 n) : z = z' :=
  Subtype.ext (funext h)

/-- `Φ_T` on a chain map `g : L → L'`: `z ↦ (g ⊗ 1) z`. -/
def PhiMap {T : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} (g : L ⟶ L') :
    Phi C T L →ₗ[k] Phi C T L' where
  toFun z := ⟨fun n => (g.f n).hom.rTensor _ (z.1 n), fun n => by
    change (Linear.rightComp k T (C.d n (n + 1))).lTensor _ ((g.f n).hom.rTensor _ (z.1 n)) =
      (L'.d (n + 1) n).hom.rTensor _ ((g.f (n + 1)).hom.rTensor _ (z.1 (n + 1)))
    rw [lTensor_rTensor_apply, z.2 n, ← LinearMap.rTensor_comp_apply,
      ← LinearMap.rTensor_comp_apply, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
      g.comm (n + 1) n]⟩
  map_add' a b := Phi_ext fun n => LinearMap.map_add _ (a.1 n) (b.1 n)
  map_smul' c a := Phi_ext fun n => LinearMap.map_smul _ c (a.1 n)

lemma PhiMap_apply {T : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} (g : L ⟶ L')
    (z : Phi C T L) (n : ℕ) : (PhiMap g z).1 n = (g.f n).hom.rTensor _ (z.1 n) := rfl

lemma PhiMap_comp {T : B} {L L' L'' : ChainComplex (ModuleCat.{u} k) ℕ} (g : L ⟶ L')
    (g' : L' ⟶ L'') (z : Phi C T L) : PhiMap (g ≫ g') z = PhiMap g' (PhiMap g z) :=
  Phi_ext fun n => by simp [PhiMap_apply, LinearMap.rTensor_comp_apply]

lemma PhiMap_id {T : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (z : Phi C T L) :
    PhiMap (𝟙 L) z = z :=
  Phi_ext fun n => by simp [PhiMap_apply]

lemma PhiMap_add {T : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} (g g' : L ⟶ L')
    (z : Phi C T L) : PhiMap (g + g') z = PhiMap g z + PhiMap g' z :=
  Phi_ext fun n => by simp [PhiMap_apply]

lemma PhiMap_zero {T : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} (z : Phi C T L) :
    PhiMap (0 : L ⟶ L') z = 0 :=
  Phi_ext fun n => by simp [PhiMap_apply]

lemma PhiMap_smul {T : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} (c : k) (g : L ⟶ L')
    (z : Phi C T L) : PhiMap (c • g) z = c • PhiMap g z :=
  Phi_ext fun n => by simp [PhiMap_apply]

lemma PhiMap_sum {T : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → (L ⟶ L')) (z : Phi C T L) : PhiMap (∑ i ∈ s, g i) z = ∑ i ∈ s, PhiMap (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PhiMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PhiMap_add, ih]

/-- `Φ` on a map `h : T' → T`: `z ↦ (1 ⊗ h^*) z`. -/
def PhiPre {T T' : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (h : T' ⟶ T) :
    Phi C T L →ₗ[k] Phi C T' L where
  toFun z := ⟨fun n => (Linear.leftComp k (C.X n) h).lTensor _ (z.1 n), fun n => by
    change (Linear.rightComp k T' (C.d n (n + 1))).lTensor _
        ((Linear.leftComp k (C.X n) h).lTensor _ (z.1 n)) =
      (L.d (n + 1) n).hom.rTensor _ ((Linear.leftComp k (C.X (n + 1)) h).lTensor _ (z.1 (n + 1)))
    rw [← lTensor_rTensor_apply, ← z.2 n, ← LinearMap.lTensor_comp_apply,
      ← LinearMap.lTensor_comp_apply]
    congr 2
    exact LinearMap.ext fun x => by simp⟩
  map_add' a b := Phi_ext fun n => LinearMap.map_add _ (a.1 n) (b.1 n)
  map_smul' c a := Phi_ext fun n => LinearMap.map_smul _ c (a.1 n)

lemma PhiPre_apply {T T' : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (h : T' ⟶ T)
    (z : Phi C T L) (n : ℕ) :
    (PhiPre h z).1 n = (Linear.leftComp k (C.X n) h).lTensor _ (z.1 n) := rfl

lemma PhiPre_PhiMap {T T' : B} {L L' : ChainComplex (ModuleCat.{u} k) ℕ} (h : T' ⟶ T)
    (g : L ⟶ L') (z : Phi C T L) : PhiPre h (PhiMap g z) = PhiMap g (PhiPre h z) :=
  Phi_ext fun _ => lTensor_rTensor_apply _ _ _

lemma PhiPre_comp {T T' T'' : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (h' : T'' ⟶ T')
    (h : T' ⟶ T) (z : Phi C T L) : PhiPre (h' ≫ h) z = PhiPre h' (PhiPre h z) :=
  Phi_ext fun n => by
    rw [PhiPre_apply, PhiPre_apply, PhiPre_apply, ← LinearMap.lTensor_comp_apply]
    congr 2
    exact LinearMap.ext fun x => Category.assoc _ _ _

lemma PhiPre_id {T : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (z : Phi C T L) :
    PhiPre (𝟙 T) z = z :=
  Phi_ext fun n => by
    simp [PhiPre_apply, show Linear.leftComp k (C.X n) (𝟙 T) = LinearMap.id from
      LinearMap.ext fun x => Category.id_comp x]

lemma PhiPre_add {T T' : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (h h' : T' ⟶ T)
    (z : Phi C T L) : PhiPre (h + h') z = PhiPre h z + PhiPre h' z :=
  Phi_ext fun n => by
    simp [PhiPre_apply, show Linear.leftComp k (C.X n) (h + h') = Linear.leftComp k (C.X n) h +
      Linear.leftComp k (C.X n) h' from LinearMap.ext fun x => Preadditive.add_comp _ _ _ _ _ _]

lemma PhiPre_zero {T T' : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (z : Phi C T L) :
    PhiPre (0 : T' ⟶ T) z = 0 :=
  Phi_ext fun n => by
    rw [PhiPre_apply, show Linear.leftComp k (C.X n) (0 : T' ⟶ T) = 0 from
      LinearMap.ext fun x => zero_comp, LinearMap.lTensor_zero]; rfl

lemma PhiPre_smul {T T' : B} {L : ChainComplex (ModuleCat.{u} k) ℕ} (c : k) (h : T' ⟶ T)
    (z : Phi C T L) : PhiPre (c • h) z = c • PhiPre h z :=
  Phi_ext fun n => by
    simp [PhiPre_apply, show Linear.leftComp k (C.X n) (c • h) = c • Linear.leftComp k (C.X n) h
      from LinearMap.ext fun x => Linear.smul_comp _ _ _ _ _ _]

end Phi

/-! ### `Φ` is left exact on `Σ` -/

section Exact

variable {C : CochainComplex B ℕ} {T : B} {L' L L'' : Perf k} {f : L' ⟶ L} {g : L ⟶ L''}

lemma IsSigma.exact' (hs : IsSigma f g) (m : ℕ) :
    Function.Exact (f.hom.f m).hom (g.hom.f m).hom :=
  fun y => hs.exact m y

/-- A sequence of `Σ` splits in each degree (`L''ₘ` is free), so `- ⊗ N` keeps it injective. -/
lemma IsSigma.rTensor_injective (hs : IsSigma f g) (m : ℕ) (N : Type*) [AddCommGroup N]
    [Module k N] : Function.Injective ((f.hom.f m).hom.rTensor N) := by
  have := (L''.property.1 m).1
  obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective (g.hom.f m).hom
    (LinearMap.range_eq_top.2 (hs.surjective m))
  obtain ⟨e, he, -⟩ := (hs.exact' m).splitSurjectiveEquiv (hs.injective m) ⟨l, hl⟩
  let r := LinearMap.fst k _ _ ∘ₗ e.toLinearMap
  have hr : r ∘ₗ (f.hom.f m).hom = LinearMap.id := by
    rw [he]
    exact LinearMap.ext fun x => by simp [r]
  intro _ _ h
  have := congrArg (r.rTensor N) h
  rwa [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, hr,
    LinearMap.rTensor_id_apply, LinearMap.rTensor_id_apply] at this

lemma PhiMap_injective (hs : IsSigma f g) : Function.Injective (PhiMap (C := C) (T := T) f.hom) :=
  fun _ _ h => Phi_ext fun n => hs.rTensor_injective n _ (congrArg (fun z => z.1 n) h)

lemma PhiMap_exact (hs : IsSigma f g) (z : Phi C T L.obj) (hz : PhiMap g.hom z = 0) :
    ∃ z', PhiMap f.hom z' = z := by
  have hw : ∀ n, ∃ w, (f.hom.f n).hom.rTensor _ w = z.1 n := fun n =>
    (_root_.rTensor_exact _ (hs.exact' n) (hs.surjective n) (z.1 n)).mp
      (congrArg (fun z => z.1 n) hz)
  choose w hw using hw
  refine ⟨⟨w, fun n => ?_⟩, Phi_ext fun n => hw n⟩
  apply hs.rTensor_injective n
  rw [← lTensor_rTensor_apply, hw n, z.2 n, ← hw (n + 1), ← LinearMap.rTensor_comp_apply,
    ← LinearMap.rTensor_comp_apply, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp,
    f.hom.comm (n + 1) n]

end Exact

/-! ### Representing objects -/

section Rep

variable (C : CochainComplex B ℕ)

/-- `X` represents `T ↦ Φ_T(L)`: `Hom(T, X) ≃ Φ_T(L)`, naturally in `T`. -/
structure Rep (L : ChainComplex (ModuleCat.{u} k) ℕ) (X : B) where
  /-- The bijections. -/
  e : ∀ T : B, (T ⟶ X) ≃ Phi C T L
  nat : ∀ {T T' : B} (h : T' ⟶ T) (x : T ⟶ X), e T' (h ≫ x) = PhiPre h (e T x)

variable {C}

namespace Rep

variable {L L' L'' : ChainComplex (ModuleCat.{u} k) ℕ} {X Y Z : B}

lemma e_eq (R : Rep C L X) {T : B} (x : T ⟶ X) : R.e T x = PhiPre x (R.e X (𝟙 X)) := by
  rw [← R.nat, Category.comp_id]

lemma e_add (R : Rep C L X) {T : B} (x y : T ⟶ X) : R.e T (x + y) = R.e T x + R.e T y := by
  rw [e_eq, R.e_eq x, R.e_eq y, PhiPre_add]

lemma e_zero (R : Rep C L X) {T : B} : R.e T 0 = 0 := by
  rw [e_eq, PhiPre_zero]

lemma e_smul (R : Rep C L X) {T : B} (c : k) (x : T ⟶ X) : R.e T (c • x) = c • R.e T x := by
  rw [e_eq, R.e_eq x, PhiPre_smul]

/-- The map `X → Y` representing `Φ(g)` (Yoneda). -/
def map (R : Rep C L X) (S : Rep C L' Y) (g : L ⟶ L') : X ⟶ Y :=
  (S.e X).symm (PhiMap g (R.e X (𝟙 X)))

lemma e_map (R : Rep C L X) (S : Rep C L' Y) (g : L ⟶ L') :
    S.e X (R.map S g) = PhiMap g (R.e X (𝟙 X)) :=
  Equiv.apply_symm_apply _ _

lemma map_spec (R : Rep C L X) (S : Rep C L' Y) (g : L ⟶ L') {T : B} (x : T ⟶ X) :
    S.e T (x ≫ R.map S g) = PhiMap g (R.e T x) := by
  rw [S.nat, e_map, PhiPre_PhiMap, ← e_eq]

lemma ext' (S : Rep C L' Y) {a b : X ⟶ Y} (h : S.e X a = S.e X b) : a = b :=
  (S.e X).injective h

lemma map_comp (R : Rep C L X) (S : Rep C L' Y) (U : Rep C L'' Z) (g : L ⟶ L') (g' : L' ⟶ L'') :
    R.map S g ≫ S.map U g' = R.map U (g ≫ g') := by
  apply U.ext'
  rw [map_spec, e_map, e_map, PhiMap_comp]

lemma map_id (R : Rep C L X) : R.map R (𝟙 L) = 𝟙 X :=
  R.ext' (by rw [e_map, PhiMap_id])

/-- Two objects representing the same `Φ(L)` are isomorphic. -/
def iso (R : Rep C L X) (S : Rep C L Y) : X ≅ Y where
  hom := R.map S (𝟙 L)
  inv := S.map R (𝟙 L)
  hom_inv_id := by rw [map_comp, Category.comp_id, map_id]
  inv_hom_id := by rw [map_comp, Category.comp_id, map_id]

end Rep

end Rep

/-! ### The disc `ℂⁿ` is represented by `Cⁿ` -/

section DiscRep

variable (n : ℕ)

/-- `x ⊗ m ↦ x • m` on a component of the disc `ℂⁿ`. -/
def evD (j : ℕ) (N : Type*) [AddCommGroup N] [Module k N] :
    (disc k n).X j ⊗[k] N →ₗ[k] N :=
  (TensorProduct.lid k N).toLinearMap ∘ₗ (discS k n j).subtype.rTensor N

variable {N N' : Type*} [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']

lemma evD_tmul (j : ℕ) (x : (disc k n).X j) (m : N) : evD n j N (x ⊗ₜ m) = dv k x • m := by
  simp [evD, dv]

/-- The generator of `ℂⁿ` in degrees `n` and `n + 1` (`0` elsewhere). -/
def gD (j : ℕ) : (disc k n).X j :=
  ⟨if j = n ∨ j = n + 1 then 1 else 0, by
    split_ifs with h
    · exact mem_discS_of_eq k n j h 1
    · exact zero_mem _⟩

lemma dv_gD (j : ℕ) : dv k (gD (k := k) n j) = if j = n ∨ j = n + 1 then 1 else 0 := rfl

lemma tmul_evD {j : ℕ} (h : j = n ∨ j = n + 1) (t : (disc k n).X j ⊗[k] N) :
    gD n j ⊗ₜ evD n j N t = t := by
  induction t with
  | tmul x m =>
    rw [evD_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    exact disc_ext k (by rw [dv_smul, dv_gD, ite_eq_left h, mul_one])
  | add a b ha hb => simp [ha, hb, TensorProduct.tmul_add]

lemma disc_tensor_eq_zero {j : ℕ} (h : ¬ (j = n ∨ j = n + 1)) (t : (disc k n).X j ⊗[k] N) :
    t = 0 := by
  induction t with
  | tmul x m =>
    rw [show x = 0 from disc_ext k (by rw [dv_eq_zero k h, dv_zero]), TensorProduct.zero_tmul]
  | add a b ha hb => simp [ha, hb]

lemma evD_injective {j : ℕ} (h : j = n ∨ j = n + 1) : Function.Injective (evD (k := k) n j N) :=
  fun a b e => by rw [← tmul_evD n h a, ← tmul_evD n h b, e]

lemma evD_lTensor (j : ℕ) (φ : N →ₗ[k] N') (t : (disc k n).X j ⊗[k] N) :
    evD n j N' (φ.lTensor _ t) = φ (evD n j N t) := by
  induction t with
  | tmul x m => rw [LinearMap.lTensor_tmul, evD_tmul, evD_tmul, map_smul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

lemma evD_d (j : ℕ) (t : (disc k n).X (j + 1) ⊗[k] N) :
    evD n j N (((disc k n).d (j + 1) j).hom.rTensor N t) =
      if j = n then evD n (j + 1) N t else 0 := by
  induction t with
  | tmul x m =>
    rw [LinearMap.rTensor_tmul, evD_tmul, evD_tmul, disc_d_apply]
    split_ifs <;> simp
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    split_ifs <;> simp

lemma evD_dmap (t : (disc k n).X (n + 1) ⊗[k] N) :
    evD (n + 1) (n + 1) N (((dmap k n).f (n + 1)).hom.rTensor N t) = evD n (n + 1) N t := by
  induction t with
  | tmul x m => rw [LinearMap.rTensor_tmul, evD_tmul, evD_tmul, dv_dmap, ite_eq_left rfl]
  | add a b ha hb => simp [ha, hb]

variable (C : CochainComplex B ℕ)

omit [Linear k B] in
/-- The components of the cycle of `ℂⁿ` attached to `x : T → Cⁿ`: `x` in degree `n`, `dx` in
degree `n + 1` (and `0` elsewhere, through the shape of `C`). -/
def wD {T : B} (x : T ⟶ C.X n) (j : ℕ) : T ⟶ C.X j :=
  if h : n = j then x ≫ eqToHom (congrArg C.X h) else x ≫ C.d n j

omit [Linear k B] in
lemma wD_self {T : B} (x : T ⟶ C.X n) : wD n C x n = x := by simp [wD]

omit [Linear k B] in
lemma wD_succ {T : B} (x : T ⟶ C.X n) : wD n C x (n + 1) = x ≫ C.d n (n + 1) := by simp [wD]

omit [Linear k B] in
lemma wD_comp {T T' : B} (h : T' ⟶ T) (x : T ⟶ C.X n) (j : ℕ) :
    wD n C (h ≫ x) j = h ≫ wD n C x j := by
  unfold wD
  split_ifs <;> simp

variable (k) in
/-- `Hom(T, Cⁿ) ≃ Φ_T(ℂⁿ)`: a cycle of `ℂⁿ` is its component in degree `n`. -/
def eDisc (T : B) : (T ⟶ C.X n) ≃ Phi C T (disc k n) where
  toFun x := ⟨fun j => gD n j ⊗ₜ wD n C x j, fun j => by
    change (Linear.rightComp k T (C.d j (j + 1))).lTensor _ (gD n j ⊗ₜ wD n C x j) =
      ((disc k n).d (j + 1) j).hom.rTensor _ (gD n (j + 1) ⊗ₜ wD n C x (j + 1))
    by_cases hj : j = n ∨ j = n + 1
    · apply evD_injective n hj
      rw [evD_lTensor, evD_tmul, evD_d, Linear.rightComp_apply, dv_gD, ite_eq_left hj, one_smul]
      rcases hj with rfl | rfl
      · rw [ite_eq_left rfl, evD_tmul, dv_gD, ite_eq_left (Or.inr rfl), one_smul, wD_self, wD_succ]
      · rw [ite_eq_right (by omega), wD_succ, Category.assoc, C.d_comp_d, comp_zero]
    · exact (disc_tensor_eq_zero n hj _).trans (disc_tensor_eq_zero n hj _).symm⟩
  invFun z := evD n n _ (z.1 n)
  left_inv x := by
    change evD n n _ (gD n n ⊗ₜ wD n C x n) = x
    rw [evD_tmul, dv_gD, ite_eq_left (Or.inl rfl), one_smul, wD_self]
  right_inv z := by
    ext j
    change gD n j ⊗ₜ wD n C (evD n n _ (z.1 n)) j = z.1 j
    by_cases h1 : j = n
    · subst h1
      rw [wD_self, tmul_evD _ (Or.inl rfl)]
    by_cases h2 : j = n + 1
    · subst h2
      have := congrArg (evD n n _) (z.2 n)
      rw [evD_lTensor, evD_d, ite_eq_left rfl, Linear.rightComp_apply] at this
      rw [wD_succ, this, tmul_evD _ (Or.inr rfl)]
    · exact (disc_tensor_eq_zero n (by omega) _).trans (disc_tensor_eq_zero n (by omega) _).symm

lemma eDisc_apply {T : B} (x : T ⟶ C.X n) (j : ℕ) :
    (eDisc k n C T x).1 j = gD n j ⊗ₜ wD n C x j := rfl

lemma eDisc_nat {T T' : B} (h : T' ⟶ T) (x : T ⟶ C.X n) :
    eDisc k n C T' (h ≫ x) = PhiPre h (eDisc k n C T x) :=
  Phi_ext fun j => by
    rw [PhiPre_apply, eDisc_apply, eDisc_apply, LinearMap.lTensor_tmul, Linear.leftComp_apply,
      wD_comp]

variable (k) in
/-- `Cⁿ` represents `Φ(ℂⁿ)`. -/
def discRep : Rep C (disc k n) (C.X n) := ⟨eDisc k n C, fun h x => eDisc_nat n C h x⟩

/-- The differential of `C^•` represents `Φ(dⁿ)`. -/
lemma discRep_d : C.d n (n + 1) = (discRep k n C).map (discRep k (n + 1) C) (dmap k n) := by
  apply (discRep k (n + 1) C).ext'
  rw [Rep.e_map]
  change eDisc k (n + 1) C _ _ = _
  rw [← Equiv.eq_symm_apply]
  change _ = evD (n + 1) (n + 1) _ (((dmap k n).f (n + 1)).hom.rTensor _ (gD n (n + 1) ⊗ₜ
    wD n C (𝟙 (C.X n)) (n + 1)))
  rw [evD_dmap, evD_tmul, dv_gD, ite_eq_left (Or.inr rfl), one_smul, wD_succ, Category.id_comp]

end DiscRep

/-! ### `I(L)` is represented by a finite biproduct of the `Cⁿ` -/

section ConeRep

variable (L : Perf k)

lemma eDec_pDec_apply (n m : ℕ) (b : Bi L n) (c : Bi L m) :
    dv k (((eDec L n b ≫ pDec L m c).hom.f (n + 1)).hom (one k n)) =
      ψ L m c (n + 1) (vv L n b (n + 1)) := by
  change ψ L m c (n + 1) (dv k (one k n) • vv L n b (n + 1)) = _
  rw [dv_one, one_smul]

open Classical in
/-- The `e_{n,b}` and `p_{n,c}` are orthogonal: `p_{n,c} e_{n,b} = δ_{b,c}`. -/
lemma eDec_pDec_self (n : ℕ) (b c : Bi L n) :
    eDec L n b ≫ pDec L n c = if b = c then 𝟙 _ else 0 := by
  ext : 1
  refine disc_hom_ext (disc_ext k ?_)
  rw [eDec_pDec_apply, ψ_succ, vv_snd_succ]
  change (bas L n).coord c (bas L n b) = _
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> rfl

/-- `p_{m,c} e_{n,b} = 0` for `m ≠ n`. -/
lemma eDec_pDec_ne {n m : ℕ} (h : n ≠ m) (b : Bi L n) (c : Bi L m) :
    eDec L n b ≫ pDec L m c = 0 := by
  ext : 1
  refine disc_hom_ext (disc_ext k ?_)
  rw [eDec_pDec_apply, ψ_apply, vv_fst_ne L n b (n + 1) (by omega), map_zero, zero_add,
    Pi.single_eq_of_ne (show n + 1 ≠ m + 1 by omega)]
  rfl

/-- The index set of the decomposition of `I(L)`: pairs `(n, b)`, `b` in the basis of `Lₙ`. -/
abbrev Idx := Σ i : Fin (bound L + 1), Bi L i

lemma total' : ∑ j : Idx L, pDec L j.1 j.2 ≫ eDec L j.1 j.2 = 𝟙 (coneP L) := by
  rw [Fintype.sum_sigma, ← total L, Finset.sum_range]

lemma eDec_pDec_idx {i j : Idx L} (h : i ≠ j) : eDec L i.1 i.2 ≫ pDec L j.1 j.2 = 0 := by
  obtain ⟨n, b⟩ := i
  obtain ⟨m, c⟩ := j
  by_cases hnm : (n : ℕ) = m
  · obtain rfl : n = m := Fin.ext hnm
    rw [eDec_pDec_self, ite_eq_right (fun (hbc : b = c) => h (by rw [hbc]))]
  · exact eDec_pDec_ne L hnm b c

variable [HasFiniteBiproducts B] (C : CochainComplex B ℕ)

/-- The object `⊕_{n,b} Cⁿ` of `ℬ`. -/
abbrev coneObj : B := ⨁ fun j : Idx L => C.X j.1

/-- `Hom(T, ⊕_{n,b} Cⁿ) ≃ Φ_T(I(L))`, through `I(L) = ⊕_{n,b} ℂⁿ`. -/
def eCone (T : B) : (T ⟶ coneObj L C) ≃ Phi C T (cone L.obj) where
  toFun x := ∑ j : Idx L, PhiMap (eDec L j.1 j.2).hom (eDisc k j.1 C T (x ≫ biproduct.π _ j))
  invFun z := biproduct.lift fun j => (eDisc k j.1 C T).symm (PhiMap (pDec L j.1 j.2).hom z)
  left_inv x := by
    refine biproduct.hom_ext _ _ fun j => ?_
    rw [biproduct.lift_π, map_sum, Finset.sum_eq_single j]
    · rw [← PhiMap_comp, show (eDec L j.1 j.2).hom ≫ (pDec L j.1 j.2).hom = 𝟙 _ from
        congrArg (fun f : D k j.1 ⟶ D k j.1 => f.hom)
          ((eDec_pDec_self L _ _ _).trans (ite_eq_left rfl)), PhiMap_id,
        Equiv.symm_apply_apply]
    · intro i _ hij
      rw [← PhiMap_comp, show (eDec L i.1 i.2).hom ≫ (pDec L j.1 j.2).hom = 0 from
        congrArg (fun f : D k i.1 ⟶ D k j.1 => f.hom) (eDec_pDec_idx L hij), PhiMap_zero]
    · simp
  right_inv z := by
    simp only [biproduct.lift_π, Equiv.apply_symm_apply]
    simp_rw [← PhiMap_comp]
    rw [← PhiMap_sum]
    rw [show ∑ j : Idx L, (pDec L j.1 j.2).hom ≫ (eDec L j.1 j.2).hom = 𝟙 _ from
      (hom_sum Finset.univ (fun j : Idx L => pDec L j.1 j.2 ≫ eDec L j.1 j.2)).symm.trans
        (congrArg (fun f : coneP L ⟶ coneP L => f.hom) (total' L)), PhiMap_id]

lemma eCone_nat {T T' : B} (h : T' ⟶ T) (x : T ⟶ coneObj L C) :
    eCone L C T' (h ≫ x) = PhiPre h (eCone L C T x) := by
  simp only [eCone, Equiv.coe_fn_mk, map_sum, PhiPre_PhiMap, eDisc_nat, PhiPre_comp]

/-- `⊕_{n,b} Cⁿ` represents `Φ(I(L))`. -/
def coneRep : Rep C (cone L.obj) (coneObj L C) := ⟨eCone L C, fun h x => eCone_nat L C h x⟩

end ConeRep

/-! ### `L` is represented by a kernel -/

section KerRep

/-- `Hom(T, ker f) ≃ {x : T → X // x f = 0}`. -/
def kernelHomEquiv {X Y : B} (f : X ⟶ Y) [HasKernel f] (T : B) :
    (T ⟶ kernel f) ≃ {x : T ⟶ X // x ≫ f = 0} where
  toFun y := ⟨y ≫ kernel.ι f, by simp⟩
  invFun x := kernel.lift f x.1 x.2
  left_inv y := by ext; simp
  right_inv x := Subtype.ext (kernel.lift_ι _ _ _)

variable [HasKernels B] {C : CochainComplex B ℕ} {L : Perf k} {X Y : B} (R : Rep C (cone L.obj) X)
  (S : Rep C (cone (shift L.obj)) Y)

/-- The map `σ(I(L)) → σ(I(L[1]))` representing `I(L) → L[1] → I(L[1])`. -/
abbrev kmap : X ⟶ Y := R.map S (πP L ≫ ιP (shiftP L)).hom

omit [HasKernels B] in
lemma PhiMap_πι_ι {T : B} (z : Phi C T L.obj) :
    PhiMap (πP L ≫ ιP (shiftP L)).hom (PhiMap (ιP L).hom z) = 0 := by
  rw [← PhiMap_comp, show (ιP L).hom ≫ (πP L ≫ ιP (shiftP L)).hom = 0 from
    congrArg (fun f : L ⟶ coneP (shiftP L) => f.hom)
      (show ιP L ≫ πP L ≫ ιP (shiftP L) = 0 by rw [← Category.assoc, ιP_comp_πP, zero_comp]),
    PhiMap_zero]

/-- `Φ_T(L)` is the kernel of `Φ_T(I(L)) → Φ_T(I(L[1]))`. -/
def kerBij (T : B) :
    Phi C T L.obj ≃ {w : Phi C T (cone L.obj) // PhiMap (πP L ≫ ιP (shiftP L)).hom w = 0} :=
  Equiv.ofBijective (fun z => ⟨PhiMap (ιP L).hom z, PhiMap_πι_ι z⟩)
    ⟨fun _ _ h => PhiMap_injective (isSigma_cone L) (congrArg Subtype.val h), fun ⟨w, hw⟩ => by
      obtain ⟨z, hz⟩ := PhiMap_exact (isSigma_cone L) w
        (PhiMap_injective (isSigma_cone (shiftP L)) (by rw [← PhiMap_comp, map_zero]; exact hw))
      exact ⟨z, Subtype.ext hz⟩⟩

/-- `Hom(T, ker) ≃ Φ_T(L)`. -/
def kerE (T : B) : (T ⟶ kernel (kmap R S)) ≃ Phi C T L.obj :=
  (kernelHomEquiv _ T).trans ((Equiv.subtypeEquiv (R.e T) (fun x =>
    ⟨fun h => by rw [← Rep.map_spec, h, Rep.e_zero],
      fun h => (S.e T).injective (by rw [Rep.map_spec, h, Rep.e_zero])⟩)).trans (kerBij T).symm)

lemma kerE_spec {T : B} (y : T ⟶ kernel (kmap R S)) :
    PhiMap (ιP L).hom (kerE R S T y) = R.e T (y ≫ kernel.ι _) :=
  congrArg Subtype.val ((kerBij T).apply_symm_apply _)

lemma kerE_nat {T T' : B} (h : T' ⟶ T) (y : T ⟶ kernel (kmap R S)) :
    kerE R S T' (h ≫ y) = PhiPre h (kerE R S T y) := by
  apply PhiMap_injective (isSigma_cone L)
  rw [kerE_spec, ← PhiPre_PhiMap, kerE_spec, Category.assoc, R.nat]

/-- `ker(σ(I(L)) → σ(I(L[1])))` represents `Φ(L)`. -/
def kerRep : Rep C L.obj (kernel (kmap R S)) := ⟨kerE R S, fun h y => kerE_nat R S h y⟩

end KerRep

/-! ### The functor `σ(C^•)` and the theorem -/

section Sigma

variable (k) [HasKernels B] [HasFiniteBiproducts B] (C : CochainComplex B ℕ)

/-- `σ(C^•)(L) = Hom^•_k(L^•, C^•)`, as the kernel of `⊕_{n,b} Cⁿ → ⊕_{n,b} Cⁿ` over the
decompositions of `I(L)` and `I(L[1])`. -/
def σObj (L : Perf k) : B := kernel (kmap (coneRep L C) (coneRep (shiftP L) C))

/-- `σ(C^•)(L)` represents `Φ(L)`. -/
def σRep (L : Perf k) : Rep C L.obj (σObj k C L) := kerRep (coneRep L C) (coneRep (shiftP L) C)

/-- The functor `σ(C^•) : 𝒫 → ℬ` of p. 50. -/
def σFun : Perf k ⥤ B where
  obj := σObj k C
  map {L M} g := (σRep k C L).map (σRep k C M) g.hom
  map_id L := (σRep k C L).map_id
  map_comp f g := ((σRep k C _).map_comp (σRep k C _) (σRep k C _) f.hom g.hom).symm

lemma σ_map_spec {L M : Perf k} (g : L ⟶ M) {T : B} (x : T ⟶ (σFun k C).obj L) :
    (σRep k C M).e T (x ≫ (σFun k C).map g) = PhiMap g.hom ((σRep k C L).e T x) :=
  Rep.map_spec _ _ _ _

instance : (σFun k C).Additive where
  map_add {L M f g} := (σRep k C M).ext' (by
    change (σRep k C M).e _ ((σRep k C L).map (σRep k C M) (f + g).hom) =
      (σRep k C M).e _ ((σRep k C L).map (σRep k C M) f.hom + (σRep k C L).map (σRep k C M) g.hom)
    rw [Rep.e_add, Rep.e_map, Rep.e_map, Rep.e_map, ← PhiMap_add]
    rfl)

instance : (σFun k C).Linear k where
  map_smul {L M} f c := (σRep k C M).ext' (by
    change (σRep k C M).e _ ((σRep k C L).map (σRep k C M) (c • f).hom) =
      (σRep k C M).e _ (c • (σRep k C L).map (σRep k C M) f.hom)
    rw [Rep.e_smul, Rep.e_map, Rep.e_map, ← PhiMap_smul]
    rfl)

/-- `σ(C^•)` carries the sequences of `Σ` to kernel diagrams. -/
lemma σ_sigmaLeftExact : SigmaLeftExact (σFun k C) := by
  intro L' L L'' f g hs
  have hfg : f ≫ g = 0 := by
    ext m : 2
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (hs.exact m _).mpr ⟨x, rfl⟩)
  have key : ∀ {T : B} (x : T ⟶ (σFun k C).obj L), x ≫ (σFun k C).map g = 0 →
      PhiMap g.hom ((σRep k C L).e T x) = 0 := fun x hx =>
    (σ_map_spec k C g x).symm.trans ((congrArg ((σRep k C L'').e _) hx).trans (Rep.e_zero _))
  refine ⟨by rw [← Functor.map_comp, hfg, Functor.map_zero], ⟨KernelFork.IsLimit.ofι _ _
    (fun {T} x hx => ((σRep k C L').e T).symm (PhiMap_exact hs _ (key x hx)).choose)
    (fun {T} x hx => ((σRep k C L).e T).injective ?_) (fun {T} x hx m hm => ?_)⟩⟩
  · refine (σ_map_spec k C f _).trans ?_
    rw [Equiv.apply_symm_apply]
    exact (PhiMap_exact hs _ (key x hx)).choose_spec
  · refine (Equiv.eq_symm_apply _).mpr (PhiMap_injective hs ?_)
    exact (σ_map_spec k C f m).symm.trans ((congrArg ((σRep k C L).e T) hm).trans
      (PhiMap_exact hs _ (key x hx)).choose_spec.symm)

/-- `σ(C^•)` as an object of `Fonct_{k, Σ-sex}(𝒫, ℬ)`. -/
def σLex : Lex k B := ⟨σFun k C, ⟨inferInstance, inferInstance, σ_sigmaLeftExact k C⟩⟩

/-- `σ(C^•)(ℂⁿ) ≅ Cⁿ`: both represent `Φ(ℂⁿ)`. -/
def σIsoX (n : ℕ) : (σFun k C).obj (D k n) ≅ C.X n := Rep.iso (σRep k C (D k n)) (discRep k n C)

/-- **Theorem (p. 50, a), second half).** `ρ(σ(C^•)) = σ(C^•)(ℂ^•) ≅ C^•`. -/
def σIso : (ρ k B).obj (σLex k C) ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun n => σIsoX k C n) (by
    rintro i j (rfl : i + 1 = j)
    rw [ρ_d]
    change (σRep k C (D k i)).map (discRep k i C) (𝟙 _) ≫ C.d i (i + 1) =
      (σRep k C (D k i)).map (σRep k C (D k (i + 1))) (dmap k i) ≫
        (σRep k C (D k (i + 1))).map (discRep k (i + 1) C) (𝟙 _)
    rw [discRep_d (k := k) i C, Rep.map_comp, Rep.map_comp, Category.id_comp, Category.comp_id])

end Sigma

section Equivalence

universe v₃ u₃

variable {B' : Type u₃} [Category.{v₃} B'] [Preadditive B'] [Linear k B'] [HasKernels B']
  [HasFiniteBiproducts B']

instance : (ρ k B').EssSurj where
  mem_essImage C := ⟨σLex k C, ⟨σIso k C⟩⟩

instance : (ρ k B').IsEquivalence where

variable (k B') in
/-- **Theorem (p. 50, a)).** For `ℬ` `k`-linear with kernels and finite biproducts,
`F ↦ F(ℂ^•)` is an equivalence from the `k`-linear `Σ`-left exact functors `𝒫 → ℬ` to the
cochain complexes of `ℬ`. -/
def ρEquivalence : Lex k B' ≌ CochainComplex B' ℕ := (ρ k B').asEquivalence

end Equivalence

end

end Grothendieck.Folder137.Perfect

/-!
# Folder 137, pages 74–76: axioms a)–c) in a polynomial category with representable degrees

Axioms a)–c) of p. 74 ask that `𝐏` have finite products, that they be products in
`𝐏₁` as well, and that `𝐏₁` be additive; the page deduces that each `𝐏(X, Y)` is an
abelian group, with `(f + g) ∘ h = f ∘ h + g ∘ h`. In the graded form used above
(`PolynomialCategory`, one set `𝐏ₙ(X, Y)` per degree) this is proved here, degree by
degree, for any polynomial category whose degrees are representable on `C`:

* `pairMap_bijective`: if `C` has binary products, then for every `n` the degree-one
  projections make `X × Y` a product in `𝐏ₙ`: `𝐏ₙ(W, X × Y) ≃ 𝐏ₙ(W, X) × 𝐏ₙ(W, Y)`
  (axiom a) degreewise); `pairMap_ι`: on degree-one maps it is the pairing of `C`
  (axiom b)); `terminal_unique`: `𝐏ₙ(W, 0)` is a point.
* `add`: if `C` is moreover preadditive (axiom c)), `f + g = m ∘ (f, g)` with
  `m = pr₁ + pr₂ : X × X → X` of degree one; `add_eq` shows it is the group law of
  `Hom(Γⁿ W, X)` carried by `φ ↦ φ ∘ γₙ`, hence an abelian group law; `comp_add`:
  `(f + g) ∘ h = f ∘ h + g ∘ h` for `h` of any degree; `ι_add`: on degree one it is
  the addition of `C`.
* For the polynomial category of a `⊗-pd`-category (the Kleisli category `toPoly`),
  `PDCategory.add_eq`: this law is the addition of `Hom(Γⁿ W, X)`.

Not formalised: the total category `𝐏(X, Y) = ⊕ₙ 𝐏ₙ(X, Y)` (composition of
inhomogeneous maps needs `Γ^q` of a sum of maps of different degrees), and the
multidegree decompositions of d).
-/

namespace Grothendieck.Folder137

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace PolynomialCategory

variable (P : PolynomialCategory C)

section Products

variable [HasBinaryProducts C]

/-- The components of a map of degree `n` into `X × Y`, by the degree-one projections. -/
noncomputable def pairMap (n : ℕ) (W X Y : C) (a : P.Hom n W (X ⨯ Y)) : P.Hom n W X × P.Hom n W Y :=
  (P.comp a (P.ι prod.fst) (one_mul n), P.comp a (P.ι prod.snd) (one_mul n))

lemma pairMap_ι {W X Y : C} (v : W ⟶ X) (w : W ⟶ Y) :
    P.pairMap 1 W X Y (P.ι (prod.lift v w)) = (P.ι v, P.ι w) := by
  simp [pairMap, ← P.ι_comp]

variable {P}

lemma pairMap_rep (R : P.Representation) {n : ℕ} {W X Y : C} (φ : R.obj n W ⟶ X ⨯ Y) :
    P.pairMap n W X Y (R.rep n W _ φ) = (R.rep n W X (φ ≫ prod.fst), R.rep n W Y (φ ≫ prod.snd)) := by
  simp [pairMap, R.rep_comp]

/-- Axiom a), degreewise: `𝐏ₙ(W, X × Y) ≃ 𝐏ₙ(W, X) × 𝐏ₙ(W, Y)`. -/
theorem pairMap_bijective (R : P.Representation) (n : ℕ) (W X Y : C) : Function.Bijective (P.pairMap n W X Y) := by
  let e : (R.obj n W ⟶ X ⨯ Y) ≃ (R.obj n W ⟶ X) × (R.obj n W ⟶ Y) :=
    ⟨fun φ => (φ ≫ prod.fst, φ ≫ prod.snd), fun p => prod.lift p.1 p.2,
      fun φ => by ext <;> simp, fun p => by simp⟩
  convert (e.trans ((R.rep n W X).prodCongr (R.rep n W Y))).bijective.comp (R.rep n W _).symm.bijective
  ext1 a
  obtain ⟨φ, rfl⟩ := (R.rep n W _).surjective a
  simp [e, pairMap_rep R]

/-- The pairing `(f, g) ↦ (f, g) : W → X × Y` in degree `n`. -/
noncomputable def pairEquiv (R : P.Representation) (n : ℕ) (W X Y : C) : P.Hom n W (X ⨯ Y) ≃ P.Hom n W X × P.Hom n W Y :=
  Equiv.ofBijective _ (pairMap_bijective R n W X Y)

lemma pairEquiv_symm_rep (R : P.Representation) {n : ℕ} {W X Y : C} (φ : R.obj n W ⟶ X) (ψ : R.obj n W ⟶ Y) :
    (pairEquiv R n W X Y).symm (R.rep n W X φ, R.rep n W Y ψ) = R.rep n W _ (prod.lift φ ψ) :=
  (Equiv.symm_apply_eq _).2 (by simp [pairEquiv, pairMap_rep R])

omit [HasBinaryProducts C] in
/-- The final object of `C` is final in every degree. -/
theorem terminal_unique [HasTerminal C] (R : P.Representation) (n : ℕ) (W : C) :
    Nonempty (Unique (P.Hom n W (⊤_ C))) :=
  ⟨(R.rep n W _).symm.unique⟩

section Additive

variable [Preadditive C]

/-- The sum `f + g = m ∘ (f, g)`, with `m = pr₁ + pr₂ : X × X → X` of degree one (p. 74). -/
noncomputable def add (R : P.Representation) {n : ℕ} {W X : C} (a b : P.Hom n W X) : P.Hom n W X :=
  P.comp ((pairEquiv R n W X X).symm (a, b)) (P.ι (prod.fst + prod.snd)) (one_mul n)

lemma rep_add (R : P.Representation) {n : ℕ} {W X : C} (φ ψ : R.obj n W ⟶ X) :
    R.rep n W X (φ + ψ) = add R (R.rep n W X φ) (R.rep n W X ψ) := by
  simp [add, pairEquiv_symm_rep, ← Representation.rep_comp]

/-- The sum is the group law of `Hom(Γⁿ W, X)` carried by `φ ↦ φ ∘ γₙ`: an abelian group
law on `𝐏ₙ(W, X)`. -/
theorem add_eq (R : P.Representation) {n : ℕ} {W X : C} (a b : P.Hom n W X) :
    add R a b = R.rep n W X ((R.rep n W X).symm a + (R.rep n W X).symm b) := by
  simp [rep_add]

/-- `(f + g) ∘ h = f ∘ h + g ∘ h`, for `h` of any degree (p. 74). -/
theorem comp_add (R : P.Representation) {p q n : ℕ} {V W X : C} (h : P.Hom p V W) (a b : P.Hom q W X)
    (hn : q * p = n) : P.comp h (add R a b) hn = add R (P.comp h a hn) (P.comp h b hn) := by
  have hpair : P.comp h ((pairEquiv R q W X X).symm (a, b)) hn =
      (pairEquiv R n V X X).symm (P.comp h a hn, P.comp h b hn) := by
    rw [Equiv.eq_symm_apply]
    have hab := (pairEquiv R q W X X).apply_symm_apply (a, b)
    simp only [pairEquiv, Equiv.ofBijective_apply, pairMap, Prod.ext_iff] at hab ⊢
    simp only [P.assoc' _ _ _ (one_mul q), hab, and_self]
  rw [add, add, ← hpair, P.assoc'' _ _ _ hn]

/-- On degree one, the sum is the addition of `C` (axiom c)). -/
theorem ι_add (R : P.Representation) {W X : C} (f g : W ⟶ X) : add R (P.ι f) (P.ι g) = P.ι (f + g) := by
  rw [add, show (pairEquiv R 1 W X X).symm (P.ι f, P.ι g) = P.ι (prod.lift f g) from
    (Equiv.symm_apply_eq _).2 (by simp [pairEquiv, P.pairMap_ι]), ← P.ι_comp]
  simp

end Additive

end Products

end PolynomialCategory

/-- In the polynomial category of a `⊗-pd`-category, the sum `m ∘ (f, g)` of p. 74 is
the addition of `Hom(Γⁿ W, X)`. -/
theorem PDCategory.add_eq (G : PDCategory C) [HasBinaryProducts C] [Preadditive C] {n : ℕ}
    {W X : C} (a b : (G.Γ n).obj W ⟶ X) :
    PolynomialCategory.add G.representation (W := W) a b = a + b := by
  have h : ∀ c : (G.Γ n).obj W ⟶ X, (G.representation.rep n W X).symm c = c := fun c =>
    (Equiv.symm_apply_eq _).2 (G.representation_rep c).symm
  refine (PolynomialCategory.add_eq G.representation a b).trans ?_
  erw [h, h]
  exact G.representation_rep _

end Grothendieck.Folder137

/-!
# Folder 137, pages 79–84: the example of `k`-modules, what Mathlib reaches

The example of p. 84: `k`-modules with the divided powers `Γ(M)` form a
`⊗-pd`-category, `𝐏_p(X, Y) = Hom(Γ^p X, Y)` being the homogeneous polynomial laws of
degree `p` (Roby). Mathlib has `DividedPowerAlgebra R M`, its generators
`dp R n m = m^{[n]}`, the relations, and its functoriality, but not its grading, nor
Roby's theorem, nor the map `α_{p,q} : Γ^{pq} → Γ^p Γ^q` (whose definition needs the
universal property of `Γ^{pq}` for polynomial laws). What follows is what holds at the
level of the universal maps `γₙ = (m ↦ m^{[n]})`:

* `dp_comp_smul`: for any linear `φ : Γ(M) → N`, `m ↦ φ(m^{[n]})` is homogeneous of
  degree `n` (axiom d)); `dp_comp_map`: it is natural in `M` along degree-one maps;
* `dp_dp_smul`: the composite `m ↦ (m^{[q]})^{[p]}`, the image of `m^{[pq]}` under
  `α_{p,q}` (p. 80), is homogeneous of degree `p q` (axiom e));
* `dp_one_add`: `γ₁` is additive (degree one), and `dp_null_of_ne_zero` (Mathlib):
  `Γⁱ(0) = 0` for `i > 0`; `dp_add` (Mathlib) is the exponential formula
  `Γⁿ(X ⊕ Y) = ⊕ Γⁱ X ⊗ Γʲ Y` on generators.
-/

namespace Grothendieck.Folder137.Modules

open DividedPowerAlgebra

variable {R M N M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup M'] [Module R M']

/-- Axiom d) in the example: `m ↦ φ(m^{[n]})` is homogeneous of degree `n`. -/
theorem dp_comp_smul (φ : DividedPowerAlgebra R M →ₗ[R] N) (n : ℕ) (r : R) (m : M) :
    φ (dp R n (r • m)) = r ^ n • φ (dp R n m) := by
  rw [dp_smul, map_smul]

/-- Precomposing `m ↦ φ(m^{[n]})` with a degree-one map `f` gives `φ ∘ Γ(f)` on `γₙ`. -/
theorem dp_comp_map (φ : DividedPowerAlgebra R M' →ₗ[R] N) (f : M →ₗ[R] M') (n : ℕ) (m : M) :
    φ (dp R n (f m)) = (φ ∘ₗ (map R f).toLinearMap) (dp R n m) := by
  simp

/-- Axiom e) in the example: `m ↦ (m^{[q]})^{[p]}` is homogeneous of degree `p q`. -/
theorem dp_dp_smul (p q : ℕ) (r : R) (m : M) :
    dp R p (dp R q (r • m)) = r ^ (p * q) • dp R p (dp R q m) := by
  rw [dp_smul, dp_smul, ← pow_mul, mul_comm]

/-- `γ₁` is additive. -/
theorem dp_one_add (x y : M) : dp R 1 (x + y) = dp R 1 x + dp R 1 y :=
  (embed R M).map_add x y

end Grothendieck.Folder137.Modules
