module

public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Limits.Pi
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.Order.Sum.Order

@[expose] public section

namespace Grothendieck.Folder19

open CategoryTheory Limits

universe w v u₁ u₂

section ContreExemple

/-- An object `(X, Y)` of `Bool → Type`: `X` at `true`, `Y` at `false`. -/
def mkObj (X Y : Type) : Bool → Type
  | true => X
  | false => Y

/-- Pairs `(X, Y)` with `Y → Nonempty X`: if `Y` is inhabited, so is `X`. -/
def P : ObjectProperty (Bool → Type) := fun Z => Z false → Nonempty (Z true)

/-- The coreflection `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def Robj (Z : Bool → Type) : P.FullSubcategory :=
  ⟨mkObj (Z true) {_y : Z false // Nonempty (Z true)}, fun y => y.2⟩

/-- The hom-set bijection of the coreflection. -/
def e (X : P.FullSubcategory) (Z : Bool → Type) : (P.ι.obj X ⟶ Z) ≃ (X ⟶ Robj Z) where
  toFun φ := P.homMk fun b => match b with
    | true => φ true
    | false => TypeCat.ofHom fun q => ⟨φ false q, (X.property q).map (φ true)⟩
  invFun ψ := fun b => match b with
    | true => ψ.hom true
    | false => ψ.hom false ≫ TypeCat.ofHom Subtype.val
  left_inv φ := by
    funext b; cases b <;> rfl
  right_inv ψ := by
    apply ObjectProperty.hom_ext; funext b; cases b <;> rfl

/-- `P ↪ (Bool → Type)` is left adjoint to `(X, Y) ↦ (X, {y : Y // Nonempty X})`. -/
def adjP : P.ι ⊣ Adjunction.rightAdjointOfEquiv e (by
    intro X' X Y f g; apply ObjectProperty.hom_ext; funext b; cases b <;> rfl) :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The inclusion of `P` is coreflective. -/
instance : Coreflective P.ι where
  R := _
  adj := adjP

end ContreExemple

section BaseProduit

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂} [∀ i, Category.{v} (B i)]

variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- (3.4) The right adjoint over the product base, `g((Xᵢ)) = ∏ᵢ gᵢ(Xᵢ)`. -/
noncomputable abbrev gPi [HasProductsOfShape I A] : (∀ i, B i) ⥤ A where
  obj X := ∏ᶜ fun i => (g i).obj (X i)
  map φ := Limits.Pi.map fun i => (g i).map (φ i)

variable [HasProductsOfShape I A]

/-- (3.4) `f = (fᵢ) : A → ∏ Bᵢ` is left adjoint to `g = ∏ gᵢ`. -/
noncomputable def adjPi : Functor.pi' f ⊣ gPi g := Adjunction.mkOfHomEquiv
  { homEquiv := fun Y X =>
      { toFun := fun φ => Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)
        invFun := fun ψ i => ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
        left_inv := fun φ => by
          funext i
          simp only [Limits.Pi.lift_comp_π]
          exact Equiv.symm_apply_apply _ _
        right_inv := fun ψ => by
          refine Limits.Pi.hom_ext _ _ fun i => ?_
          simp only [Limits.Pi.lift_comp_π]
          exact Equiv.apply_symm_apply _ _ }
    homEquiv_naturality_left_symm := fun h ψ => by
      funext i
      change ((adj i).homEquiv _ _).symm ((h ≫ ψ) ≫ Limits.Pi.π _ i) =
        (f i).map h ≫ ((adj i).homEquiv _ _).symm (ψ ≫ Limits.Pi.π _ i)
      rw [Category.assoc]
      exact (adj i).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := fun φ ψ => by
      refine Limits.Pi.hom_ext _ _ fun i => ?_
      change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ ((φ ≫ ψ) i)) ≫ Limits.Pi.π _ i =
        ((Limits.Pi.lift fun i => (adj i).homEquiv _ _ (φ i)) ≫
          Limits.Pi.map (fun i => (g i).map (ψ i))) ≫ Limits.Pi.π _ i
      rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc]
      exact (adj i).homEquiv_naturality_right _ _ }

@[reassoc (attr := simp)]
theorem adjPi_unit_π (Y : A) (j : I) :
    (adjPi f g adj).unit.app Y ≫ Limits.Pi.π _ j = (adj j).unit.app Y := by
  change (Limits.Pi.lift fun i => (adj i).homEquiv _ _ (𝟙 ((f i).obj Y))) ≫ Limits.Pi.π _ j = _
  rw [Limits.Pi.lift_comp_π]
  exact (adj j).homEquiv_id Y

theorem adjPi_counit (X : ∀ i, B i) (j : I) :
    (adjPi f g adj).counit.app X j =
      (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫ (adj j).counit.app (X j) := by
  change ((adj j).homEquiv ((gPi g).obj X) (X j)).symm
    (𝟙 ((gPi g).obj X) ≫ Limits.Pi.π (fun i => (g i).obj (X i)) j) = _
  rw [Category.id_comp]
  exact (adj j).homEquiv_counit _ _ _

/-- (3.6) The entry `φ_ji = f_j g_i : B_i → B_j` of the matrix. -/
abbrev phi (j i : I) : B i ⥤ B j := g i ⋙ f j

/-- (3.10) `λ_kji : φ_ki → φ_kj φ_ji`, the unit `id → g_j f_j` inserted in the middle of
`f_k g_i`. -/
@[simps]
def lam (k j i : I) : phi f g k i ⟶ phi f g j i ⋙ phi f g k j where
  app X := (f k).map ((adj j).unit.app ((g i).obj X))
  naturality X Y h := by
    simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp]
    exact congrArg (f k).map ((adj j).unit.naturality ((g i).map h))

/-- (3.5)–(3.6) **The matrix.** If `f_j` commutes with `I`-indexed products, the
`j`-th component of `φ((Xᵢ))` is the product of the `φ_ji(Xᵢ)`, with projections
`f_j(prᵢ)`. -/
noncomputable def matrice (X : ∀ i, B i) (j : I) [PreservesLimitsOfShape (Discrete I) (f j)] :
    IsLimit (Fan.mk ((adjPi f g adj).toComonad.obj X j)
      fun i => (f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)) :=
  (isLimitMapConeFanMkEquiv (f j) _ _) (isLimitOfPreserves (f j) (productIsProduct _))

/-- (3.9), first line: the counit of `φ` is diagonal, `ᾱ_k = α_k(X_k) ∘ pr_k`. -/
theorem counit_matrice (X : ∀ i, B i) (k : I) :
    (adjPi f g adj).toComonad.ε.app X k =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) k) ≫ (adj k).counit.app (X k) :=
  adjPi_counit f g adj X k

/-- (3.9), second line: the `(k, j, i)` entry of the comultiplication of `φ` is
`λ̄_kji = λ_kji(Xᵢ) ∘ prᵢ`. -/
theorem comult_matrice (X : ∀ i, B i) (k j i : I) :
    (adjPi f g adj).toComonad.δ.app X k ≫
        (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i))) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (lam f g adj k j i).app (X i) := by
  have h1 := adjPi_unit_π_assoc f g adj ((gPi g).obj X) j
    ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))
  have h2 := (adj j).unit.naturality (Limits.Pi.π (fun i => (g i).obj (X i)) i)
  have h3 := congrArg (f k).map (h1.trans h2.symm)
  exact (((f k).map_comp _ _).symm.trans h3).trans ((f k).map_comp _ _)

section PleinementFideles

omit [HasProductsOfShape I A] in
/-- If `g_i` is fully faithful, the diagonal entry `φ_ii = f_i g_i` is the identity
(through the counit). -/
noncomputable def diagIso (i : I) [(g i).Full] [(g i).Faithful] : phi f g i i ≅ 𝟭 (B i) :=
  asIso (adj i).counit

omit [HasProductsOfShape I A] in
/-- (3.11 b), (3.14) The unit `λ' : id_{B_i} → φ_ij φ_ji` (`i ≠ j`) when `g_i` is
fully faithful: `λ_iji` read through `φ_ii ≅ id`. -/
noncomputable def lamUnit (i j : I) [(g i).Full] [(g i).Faithful] :
    𝟭 (B i) ⟶ phi f g j i ⋙ phi f g i j :=
  (diagIso f g adj i).inv ≫ lam f g adj i j i

end PleinementFideles

end BaseProduit

section MatriceRelations

variable {I : Type w} {A : Type u₁} [Category.{v} A] {B : I → Type u₂}
  [∀ i, Category.{v} (B i)]

variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

/-- Right counit relation: `φ_ki(α_i) ∘ λ_kii = id`. -/
theorem lam_counit_right (k i : I) (X : B i) :
    (lam f g adj k i i).app X ≫ (phi f g k i).map ((adj i).counit.app X) = 𝟙 _ := by
  simp only [lam_app, Functor.comp_map, ← Functor.map_comp, Adjunction.right_triangle_components]
  exact (f k).map_id _

/-- Left counit relation: `α_k φ_ki ∘ λ_kki = id`. -/
theorem lam_counit_left (k i : I) (X : B i) :
    (lam f g adj k k i).app X ≫ (adj k).counit.app ((phi f g k i).obj X) = 𝟙 _ := by
  simp only [lam_app]
  exact (adj k).left_triangle_components _

/-- `l ≫ e = 𝟙` and `e ≫ i = 𝟙` give `l = i`. -/
theorem eq_of_comp_eq_id {C : Type*} [Category C] {X Y : C} (l : X ⟶ Y) (e : Y ⟶ X)
    (i : X ⟶ Y) (h1 : l ≫ e = 𝟙 X) (h2 : e ≫ i = 𝟙 Y) : l = i := by
  rw [← Category.comp_id l, ← h2, ← Category.assoc, h1, Category.id_comp]

/-- With `g_i` fully faithful, `λ_kii = φ_ki(α_i⁻¹)`. -/
theorem lam_app_right (k i : I) [(g i).Full] [(g i).Faithful] (X : B i) :
    (lam f g adj k i i).app X = (phi f g k i).map ((diagIso f g adj i).inv.app X) :=
  eq_of_comp_eq_id _ ((phi f g k i).map ((adj i).counit.app X)) _ (lam_counit_right f g adj k i X)
    (((phi f g k i).map_comp _ _).symm.trans
      ((congrArg (phi f g k i).map ((diagIso f g adj i).hom_inv_id_app X)).trans
        ((phi f g k i).map_id _)))

/-- With `g_k` fully faithful, `λ_kki = α_k⁻¹ φ_ki`. -/
theorem lam_app_left (k i : I) [(g k).Full] [(g k).Faithful] (X : B i) :
    (lam f g adj k k i).app X = (diagIso f g adj k).inv.app ((phi f g k i).obj X) :=
  eq_of_comp_eq_id _ ((adj k).counit.app ((phi f g k i).obj X)) _ (lam_counit_left f g adj k i X)
    ((diagIso f g adj k).hom_inv_id_app _)

/-- Naturality of `α_k⁻¹ : id → φ_kk`. -/
theorem diag_nat (k : I) [(g k).Full] [(g k).Faithful] {Y Z : B k} (h : Y ⟶ Z) :
    (diagIso f g adj k).inv.app Y ≫ (phi f g k k).map h = h ≫ (diagIso f g adj k).inv.app Z :=
  ((diagIso f g adj k).inv.naturality h).symm

/-- A relation `(k, i, i)`, automatic once the diagonal entry is `α_i⁻¹`. -/
theorem rel_right (k i : I) [(g i).Full] [(g i).Faithful] {Y : B k} {X : B i}
    (u : Y ⟶ (phi f g k i).obj X) :
    u ≫ (lam f g adj k i i).app X = u ≫ (phi f g k i).map ((diagIso f g adj i).inv.app X) := by
  rw [lam_app_right]

/-- A relation `(k, k, i)`, automatic once the diagonal entry is `α_k⁻¹`. -/
theorem rel_left (k i : I) [(g k).Full] [(g k).Faithful] {Y : B k} {X : B i}
    (u : Y ⟶ (phi f g k i).obj X) :
    u ≫ (lam f g adj k k i).app X = (diagIso f g adj k).inv.app Y ≫ (phi f g k k).map u := by
  rw [lam_app_left, diag_nat]

/-- The relation `(i, j, i)` with diagonal entry `α_i⁻¹` is the triangle of `λ'`. -/
theorem rel_unit (i j : I) [(g i).Full] [(g i).Faithful] (X : B i) :
    (diagIso f g adj i).inv.app X ≫ (lam f g adj i j i).app X = (lamUnit f g adj i j).app X :=
  rfl

variable [HasProductsOfShape I A]

/-- The comonad `φ = fg` over the product base. -/
noncomputable abbrev comPi : Comonad (∀ i, B i) := (adjPi f g adj).toComonad

/-- The entries `u_ki = a_k ≫ f_k(prᵢ)` of a morphism `a : X → φX`. -/
noncomputable def entree {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) (k i : I) :
    X k ⟶ (phi f g k i).obj (X i) :=
  a k ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)

/-- **The counit, entry by entry**: `a` is counital iff `α_k ∘ u_kk = id` for all `k`. -/
theorem counit_iff {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) :
    a ≫ (comPi f g adj).ε.app X = 𝟙 X ↔
      ∀ k, entree f g adj a k k ≫ (adj k).counit.app (X k) = 𝟙 _ := by
  constructor
  · intro h k
    exact (Category.assoc _ _ _).trans
      ((congrArg (a k ≫ ·) (counit_matrice f g adj X k)).symm.trans (congrFun h k))
  · intro h
    funext k
    exact (congrArg (a k ≫ ·) (counit_matrice f g adj X k)).trans
      ((Category.assoc _ _ _).symm.trans (h k))

/-- The `(j, i)` test morphisms on `φ²X`, at component `k`. -/
noncomputable abbrev test2 (X : ∀ i, B i) (k j i : I) :
    ((comPi f g adj).obj ((comPi f g adj).obj X)) k ⟶
      (phi f g k j).obj ((phi f g j i).obj (X i)) :=
  (f k).map (Limits.Pi.π _ j ≫ (g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))

/-- Morphisms into `(φ²X)_k` are determined by the test morphisms `test2`. -/
theorem ext_phi2 [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] (X : ∀ i, B i) (k : I)
    {T : B k} (t t' : T ⟶ ((comPi f g adj).obj ((comPi f g adj).obj X)) k)
    (h : ∀ j i, t ≫ test2 f g adj X k j i = t' ≫ test2 f g adj X k j i) : t = t' := by
  have hk := (isLimitMapConeFanMkEquiv (f k) _ _)
    (isLimitOfPreserves (f k) (productIsProduct
      (fun j => (g j).obj ((f j).obj ((gPi g).obj X)))))
  refine Fan.IsLimit.hom_ext hk _ _ fun j => ?_
  have : PreservesLimitsOfShape (Discrete I) (g j) := (adj j).rightAdjoint_preservesLimits.1
  have hj := (isLimitMapConeFanMkEquiv (f j ⋙ g j ⋙ f k) _ _)
    (isLimitOfPreserves (f j ⋙ g j ⋙ f k) (productIsProduct (fun i => (g i).obj (X i))))
  refine Fan.IsLimit.hom_ext hj _ _ fun i => ?_
  have e : t ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) =
      t' ≫ ((f k).map (Limits.Pi.π
        (fun j => (g j).obj ((f j).obj ((gPi g).obj X))) j) ≫
        (f k).map ((g j).map ((f j).map (Limits.Pi.π (fun i => (g i).obj (X i)) i)))) := by
    exact (congrArg (t ≫ ·) ((f k).map_comp _ _).symm).trans
      ((h j i).trans (congrArg (t' ≫ ·) ((f k).map_comp _ _)))
  exact (Category.assoc _ _ _).trans (e.trans (Category.assoc _ _ _).symm)

/-- `φ(a)` read on the test morphisms. -/
theorem map_test2 {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X) (k j i : I) :
    (comPi f g adj).map a k ≫ test2 f g adj X k j i =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) j) ≫
        (phi f g k j).map (entree f g adj a j i) := by
  change (f k).map (Limits.Pi.map fun j => (g j).map (a j)) ≫ _ = _
  simp only [test2, entree, Functor.comp_map, ← Functor.map_comp, Limits.Pi.map_π_assoc]
  exact congrArg (fun x => (f k).map (Limits.Pi.π (fun j => (g j).obj (X j)) j ≫ x))
    ((g j).map_comp _ _).symm

/-- `φ(h)` read on the projections. -/
theorem map_π {X Y : ∀ i, B i} (h : X ⟶ Y) (k i : I) :
    (comPi f g adj).map h k ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i) =
      (f k).map (Limits.Pi.π (fun i => (g i).obj (X i)) i) ≫ (phi f g k i).map (h i) := by
  change (f k).map (Limits.Pi.map fun j => (g j).map (h j)) ≫ _ = _
  simp only [Functor.comp_map, ← Functor.map_comp, Limits.Pi.map_π]

/-- **Coassociativity as relations between the `λ_kji`**: `a` is coassociative iff
`λ_kji ∘ u_ki = φ_kj(u_ji) ∘ u_kj` for all `k, j, i`. -/
theorem coassoc_iff [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] {X : ∀ i, B i}
    (a : X ⟶ (comPi f g adj).obj X) :
    a ≫ (comPi f g adj).δ.app X = a ≫ (comPi f g adj).map a ↔
      ∀ k j i, entree f g adj a k i ≫ (lam f g adj k j i).app (X i) =
        entree f g adj a k j ≫ (phi f g k j).map (entree f g adj a j i) := by
  have h1 : ∀ k j i, a k ≫ ((comPi f g adj).δ.app X k ≫ test2 f g adj X k j i) =
      entree f g adj a k i ≫ (lam f g adj k j i).app (X i) := fun k j i =>
    (congrArg (a k ≫ ·) (comult_matrice f g adj X k j i)).trans (Category.assoc _ _ _).symm
  have h2 : ∀ k j i, a k ≫ ((comPi f g adj).map a k ≫ test2 f g adj X k j i) =
      entree f g adj a k j ≫ (phi f g k j).map (entree f g adj a j i) := fun k j i =>
    (congrArg (a k ≫ ·) (map_test2 f g adj a k j i)).trans (Category.assoc _ _ _).symm
  constructor
  · intro h k j i
    have := congrArg (fun x => x ≫ test2 f g adj X k j i) (congrFun h k)
    exact (h1 k j i).symm.trans ((Category.assoc _ _ _).symm.trans
      (this.trans ((Category.assoc _ _ _).trans (h2 k j i))))
  · intro h
    funext k
    refine ext_phi2 f g adj X k _ _ fun j i => ?_
    exact (Category.assoc _ _ _).trans ((h1 k j i).trans ((h k j i).trans
      ((h2 k j i).symm.trans (Category.assoc _ _ _).symm)))

/-- Morphisms of coalgebras, entry by entry. -/
theorem hom_iff [∀ j, PreservesLimitsOfShape (Discrete I) (f j)] {X Y : ∀ i, B i}
    (a : X ⟶ (comPi f g adj).obj X) (b : Y ⟶ (comPi f g adj).obj Y) (h : X ⟶ Y) :
    a ≫ (comPi f g adj).map h = h ≫ b ↔
      ∀ k i, entree f g adj a k i ≫ (phi f g k i).map (h i) = h k ≫ entree f g adj b k i := by
  have h1 : ∀ k i, a k ≫ ((comPi f g adj).map h k ≫
      (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i)) =
      entree f g adj a k i ≫ (phi f g k i).map (h i) := fun k i =>
    (congrArg (a k ≫ ·) (map_π f g adj h k i)).trans (Category.assoc _ _ _).symm
  constructor
  · intro e k i
    have := congrArg (fun x => x ≫ (f k).map (Limits.Pi.π (fun i => (g i).obj (Y i)) i))
      (congrFun e k)
    exact (h1 k i).symm.trans ((Category.assoc _ _ _).symm.trans
      (this.trans (Category.assoc _ _ _)))
  · intro e
    funext k
    refine Fan.IsLimit.hom_ext (matrice f g adj Y k) _ _ fun i => ?_
    exact (Category.assoc _ _ _).trans ((h1 k i).trans ((e k i).trans
      (Category.assoc _ _ _).symm))

/-- Counit of a coalgebra, with `g_k` fully faithful: the diagonal entry is `α_k⁻¹`. -/
theorem entree_diag {X : ∀ i, B i} (a : X ⟶ (comPi f g adj).obj X)
    (ha : a ≫ (comPi f g adj).ε.app X = 𝟙 X) (k : I) [(g k).Full] [(g k).Faithful] :
    entree f g adj a k k = (diagIso f g adj k).inv.app (X k) :=
  eq_of_comp_eq_id _ ((adj k).counit.app (X k)) _ ((counit_iff f g adj a).1 ha k)
    ((diagIso f g adj k).hom_inv_id_app _)

end MatriceRelations

section Quadruplets

variable {A : Type u₁} [Category.{v} A] {B : WalkingPair → Type u₂}
  [∀ i, Category.{v} (B i)]

variable (f : ∀ i, A ⥤ B i) (g : ∀ i, B i ⥤ A) (adj : ∀ i, f i ⊣ g i)

variable [(g .left).Full] [(g .left).Faithful] [(g .right).Full] [(g .right).Faithful]

/-- (pages 9–10) A quadruple `(X', X'', u', u'')`, `u' : X' → φ'(X'')`,
`u'' : X'' → φ''(X')`, subject to the two triangles `λ'(X') = φ'(u'') ∘ u'` and
`λ''(X'') = φ''(u') ∘ u''`. -/
structure Quadruplet where
  X' : B .left
  X'' : B .right
  u' : X' ⟶ (phi f g .left .right).obj X''
  u'' : X'' ⟶ (phi f g .right .left).obj X'
  tri' : (lamUnit f g adj .left .right).app X' = u' ≫ (phi f g .left .right).map u''
  tri'' : (lamUnit f g adj .right .left).app X'' = u'' ≫ (phi f g .right .left).map u'

namespace Quadruplet

variable {f g adj}

/-- A morphism of quadruples: a pair `(h', h'')` commuting with `u'` and `u''`. -/
@[ext]
structure Hom (P Q : Quadruplet f g adj) where
  h' : P.X' ⟶ Q.X'
  h'' : P.X'' ⟶ Q.X''
  w' : P.u' ≫ (phi f g .left .right).map h'' = h' ≫ Q.u' := by cat_disch
  w'' : P.u'' ≫ (phi f g .right .left).map h' = h'' ≫ Q.u'' := by cat_disch

attribute [reassoc] Hom.w' Hom.w''

instance : Category (Quadruplet f g adj) where
  Hom := Hom
  id P := { h' := 𝟙 _, h'' := 𝟙 _ }
  comp a b := { h' := a.h' ≫ b.h', h'' := a.h'' ≫ b.h''
                w' := by
                  rw [Functor.map_comp, ← Category.assoc, a.w', Category.assoc, b.w',
                    Category.assoc]
                w'' := by
                  rw [Functor.map_comp, ← Category.assoc, a.w'', Category.assoc, b.w'',
                    Category.assoc] }

@[ext]
theorem hom_ext {P Q : Quadruplet f g adj} {a b : P ⟶ Q} (h' : a.h' = b.h')
    (h'' : a.h'' = b.h'') : a = b := Hom.ext h' h''

end Quadruplet

variable [HasProductsOfShape WalkingPair A]

variable [∀ j, PreservesLimitsOfShape (Discrete WalkingPair) (f j)]

/-- A morphism given by its two components. -/
def pairHom {X Y : ∀ i, B i} (h' : X .left ⟶ Y .left) (h'' : X .right ⟶ Y .right) : X ⟶ Y
  | .left => h'
  | .right => h''

/-- (pages 9–10) A coalgebra of `φ` gives the quadruple of its off-diagonal entries. -/
noncomputable def versQuadruplets : (comPi f g adj).Coalgebra ⥤ Quadruplet f g adj where
  obj C :=
    { X' := C.A .left
      X'' := C.A .right
      u' := entree f g adj C.a .left .right
      u'' := entree f g adj C.a .right .left
      tri' := by
        have := (coassoc_iff f g adj C.a).1 C.coassoc .left .right .left
        rw [entree_diag f g adj C.a C.counit] at this
        exact this
      tri'' := by
        have := (coassoc_iff f g adj C.a).1 C.coassoc .right .left .right
        rw [entree_diag f g adj C.a C.counit] at this
        exact this }
  map {C D} h :=
    { h' := h.f .left
      h'' := h.f .right
      w' := (hom_iff f g adj C.a D.a h.f).1 h.h .left .right
      w'' := (hom_iff f g adj C.a D.a h.f).1 h.h .right .left }

/-- An object of `B' × B''` given by its two components. -/
def pairObj (X' : B .left) (X'' : B .right) : ∀ i, B i
  | .left => X'
  | .right => X''

variable {f g adj} in
/-- The matrix of a quadruple: `α⁻¹` on the diagonal, `u'` and `u''` off it. -/
noncomputable def entreesQ (Q : Quadruplet f g adj) :
    ∀ k i, pairObj Q.X' Q.X'' k ⟶ (phi f g k i).obj (pairObj Q.X' Q.X'' i)
  | .left, .left => (diagIso f g adj .left).inv.app Q.X'
  | .left, .right => Q.u'
  | .right, .left => Q.u''
  | .right, .right => (diagIso f g adj .right).inv.app Q.X''

variable {f g adj} in
/-- The coalgebra structure defined by a quadruple. -/
noncomputable def structQ (Q : Quadruplet f g adj) :
    pairObj Q.X' Q.X'' ⟶ (comPi f g adj).obj (pairObj Q.X' Q.X'') := fun k =>
  Fan.IsLimit.lift (matrice f g adj (pairObj Q.X' Q.X'') k) (entreesQ Q k)

/-- The entries of `structQ Q` are those of `entreesQ Q`. -/
theorem entree_structQ (Q : Quadruplet f g adj) (k i : WalkingPair) :
    entree f g adj (structQ Q) k i = entreesQ Q k i :=
  Fan.IsLimit.fac (matrice f g adj (pairObj Q.X' Q.X'') k) _ i

variable {f g adj} in
/-- **The quadruple defines a coalgebra**: the triangles are all the coassociativity. -/
noncomputable def coalgQ (Q : Quadruplet f g adj) : (comPi f g adj).Coalgebra where
  A := pairObj Q.X' Q.X''
  a := structQ Q
  counit := (counit_iff f g adj _).2 fun k => by
    rw [entree_structQ]
    cases k
    · exact (diagIso f g adj .left).inv_hom_id_app Q.X'
    · exact (diagIso f g adj .right).inv_hom_id_app Q.X''
  coassoc := (coassoc_iff f g adj _).2 fun k j i => by
    rw [entree_structQ, entree_structQ, entree_structQ]
    cases k <;> cases j <;> cases i
    · exact rel_right f g adj _ _ _
    · exact rel_left f g adj _ _ Q.u'
    · exact (rel_unit f g adj _ _ _).trans Q.tri'
    · exact rel_right f g adj _ _ Q.u'
    · exact rel_right f g adj _ _ Q.u''
    · exact (rel_unit f g adj _ _ _).trans Q.tri''
    · exact rel_left f g adj _ _ Q.u''
    · exact rel_right f g adj _ _ _

instance : (versQuadruplets f g adj).Faithful where
  map_injective {C D} a b e := by
    refine Comonad.Coalgebra.Hom.ext (funext fun j => ?_)
    cases j
    · exact congrArg Quadruplet.Hom.h' e
    · exact congrArg Quadruplet.Hom.h'' e

instance : (versQuadruplets f g adj).Full where
  map_surjective {C D} q := by
    refine ⟨⟨pairHom q.h' q.h'', (hom_iff f g adj C.a D.a _).2 fun k i => ?_⟩, rfl⟩
    cases k <;> cases i
    · rw [entree_diag f g adj C.a C.counit, entree_diag f g adj D.a D.counit]
      exact diag_nat f g adj _ q.h'
    · exact q.w'
    · exact q.w''
    · rw [entree_diag f g adj C.a C.counit, entree_diag f g adj D.a D.counit]
      exact diag_nat f g adj _ q.h''

instance : (versQuadruplets f g adj).EssSurj where
  mem_essImage Q := ⟨coalgQ Q, ⟨
    { hom := { h' := 𝟙 _, h'' := 𝟙 _
               w' := ((congrArg (_ ≫ ·) ((phi f g .left .right).map_id _)).trans
                 ((Category.comp_id _).trans
                   ((entree_structQ f g adj Q .left .right).trans (Category.id_comp _).symm)))
               w'' := ((congrArg (_ ≫ ·) ((phi f g .right .left).map_id _)).trans
                 ((Category.comp_id _).trans
                   ((entree_structQ f g adj Q .right .left).trans (Category.id_comp _).symm))) }
      inv := { h' := 𝟙 _, h'' := 𝟙 _
               w' := ((congrArg (_ ≫ ·) ((phi f g .left .right).map_id _)).trans
                 ((Category.comp_id _).trans ((entree_structQ f g adj Q .left .right).symm.trans
                   (Category.id_comp _).symm)))
               w'' := ((congrArg (_ ≫ ·) ((phi f g .right .left).map_id _)).trans
                 ((Category.comp_id _).trans ((entree_structQ f g adj Q .right .left).symm.trans
                   (Category.id_comp _).symm))) }
      hom_inv_id := by ext <;> exact Category.comp_id _
      inv_hom_id := by ext <;> exact Category.comp_id _ }⟩⟩

/-- **Pages 9–10: coalgebras of `φ` are the quadruples.** For two factors with `g'`, `g''`
fully faithful and `f'`, `f''` commuting with binary products, the category of coalgebras
of `φ` is equivalent to the category of quadruples `(X', X'', u', u'')`. -/
instance versQuadruplets_isEquivalence : (versQuadruplets f g adj).IsEquivalence where

/-- **Pages 9–10: the description of `A` by quadruples.** If moreover `f = (f', f'')` is
comonadic, `A` is equivalent to the category of quadruples, by
`Y ↦ (f'Y, f''Y, f'(η''_Y), f''(η'_Y))` (`quadruplet_u'`, `quadruplet_u''`). -/
theorem quadruplets [(Comonad.comparison (adjPi f g adj)).IsEquivalence] :
    (Comonad.comparison (adjPi f g adj) ⋙ versQuadruplets f g adj).IsEquivalence := by
  sorry

end Quadruplets

end Grothendieck.Folder19
