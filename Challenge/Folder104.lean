module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

namespace Grothendieck.Folder104

open CategoryTheory

/-- **Example 3**, the hemispherical disc `D_n`: `I_n = (Δ_{n-1} × {±1}) ⊔ {d_n}`
(`none` is `d_n`). -/
def Hemi (n : ℕ) : Type := Option (Fin n × Bool)

instance (n : ℕ) : Fintype (Hemi n) := inferInstanceAs (Fintype (Option (Fin n × Bool)))

instance (n : ℕ) : DecidableEq (Hemi n) := inferInstanceAs (DecidableEq (Option (Fin n × Bool)))

/-- The order of the cells: `(k, ε) < (k', ε')` iff `k < k'`, `d_n` on top. -/
def Hemi.le {n : ℕ} : Hemi n → Hemi n → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a = b ∨ a.1 < b.1

instance (n : ℕ) : PartialOrder (Hemi n) where
  le := Hemi.le
  le_refl a := by cases a <;> simp [Hemi.le]
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp only [Hemi.le, imp_self, implies_true,
      IsEmpty.forall_iff]
    rename_i a b c
    rintro (rfl | h₁) (rfl | h₂)
    · exact Or.inl rfl
    · exact Or.inr h₂
    · exact Or.inr h₁
    · exact Or.inr (h₁.trans h₂)
  le_antisymm a b := by
    cases a <;> cases b <;> simp only [Hemi.le, IsEmpty.forall_iff, forall_const]
    · rfl
    rename_i a b
    rintro (rfl | h₁) (h₂ | h₂)
    · rfl
    · rfl
    · exact h₂.symm ▸ rfl
    · exact absurd (h₁.trans h₂) (lt_irrefl _)

section Epinglage

open Opposite Limits

universe w

variable {M : Type w} [SmallCategory M]

/-- `I_D`: the sub-objects of `D` in a skeletal `M` satisfying (i) and (ii), that is, by (*),
the arrows `D' → D`. -/
abbrev Sous (D : M) : Type w := Σ D' : M, (D' ⟶ D)

/-- The order of `I_D`: `(D', a) ≤ (D'', b)` iff `a` factors through `b`. -/
def Sous.le {D : M} (y y' : Sous D) : Prop := ∃ w : y.1 ⟶ y'.1, w ≫ y'.2 = y.2

variable (M) in
/-- **An `M`-pinned poset** (pages 12–13): a poset `K`, a strictly increasing type map
`τ_K : K → N` (here `N` is the skeletal `M` itself, ordered by the existence of an arrow), and
for each `ξ` of type `n` an isomorphism `u_ξ : I_n ≅ K_{≤ξ}` with `u_ξ(d_n) = ξ`, satisfying
(1) `τ_K ∘ u_ξ = τ_n` and (2) `u_ξ ∘ u^n_y = u_{u_ξ(y)}`. -/
structure Epingle where
  /-- The poset. -/
  K : Type w
  [ordre : PartialOrder K]
  /-- The type map `τ_K`. -/
  τ : K → M
  τ_strict : ∀ ξ η : K, ξ < η → Nonempty (τ ξ ⟶ τ η) ∧ τ ξ ≠ τ η
  /-- The pinning `u_ξ : I_{τ ξ} → K`. -/
  u : (ξ : K) → Sous (τ ξ) → K
  u_top : ∀ ξ, u ξ ⟨τ ξ, 𝟙 _⟩ = ξ
  u_injective : ∀ ξ, Function.Injective (u ξ)
  u_range : ∀ ξ, Set.range (u ξ) = Set.Iic ξ
  u_le : ∀ ξ y y', u ξ y ≤ u ξ y' ↔ Sous.le y y'
  /-- (1) -/
  τ_u : ∀ ξ y, τ (u ξ y) = y.1
  /-- (2) -/
  u_u : ∀ ξ (y : Sous (τ ξ)) (z : Sous y.1),
    u (u ξ y) ⟨z.1, z.2 ≫ eqToHom (τ_u ξ y).symm⟩ = u ξ ⟨z.1, z.2 ≫ y.2⟩

attribute [instance] Epingle.ordre

/-- The morphisms of `M`-pinned posets (page 13): strictly increasing maps `f` with
`τ_L ∘ f = τ_K` making the triangles `u^L_{f ξ} = f ∘ u^K_ξ` commute. -/
@[ext]
structure Epingle.Hom (K L : Epingle M) where
  /-- The underlying map. -/
  f : K.K → L.K
  strictMono : StrictMono f
  τ_f : ∀ ξ, L.τ (f ξ) = K.τ ξ
  u_f : ∀ ξ y, f (K.u ξ y) = L.u (f ξ) ⟨y.1, y.2 ≫ eqToHom (τ_f ξ).symm⟩

instance : Category (Epingle M) where
  Hom := Epingle.Hom
  id K := ⟨id, strictMono_id, fun _ => rfl, fun _ _ => by simp⟩
  comp φ ψ := ⟨ψ.f ∘ φ.f, ψ.strictMono.comp φ.strictMono,
    fun ξ => (ψ.τ_f _).trans (φ.τ_f ξ), fun ξ y => by simp [φ.u_f, ψ.u_f]⟩

@[ext]
lemma Epingle.hom_ext {K L : Epingle M} {φ ψ : K ⟶ L} (h : φ.f = ψ.f) : φ = ψ :=
  Epingle.Hom.ext h

@[simp] lemma Epingle.id_f (K : Epingle M) : Epingle.Hom.f (𝟙 K) = id := rfl

@[simp] lemma Epingle.comp_f {K L N : Epingle M} (φ : K ⟶ L) (ψ : L ⟶ N) :
    (φ ≫ ψ).f = ψ.f ∘ φ.f := rfl

end Epinglage

section Prefaisceaux

open Opposite Limits

universe w

variable {M : Type w} [SmallCategory M]

/-- A presheaf is **non-singular** when each of its elements `x ∈ X(D)` is a monomorphism
`yoneda D → X`, that is, `a ↦ X(a)(x)` is injective. -/
def NonSingulier (X : Mᵒᵖ ⥤ Type w) : Prop :=
  ∀ ⦃D D' : M⦄ (x : X.obj (op D)) (a b : D' ⟶ D), X.map a.op x = X.map b.op x → a = b

/-- A sub-object of `X` is a *model* if it is isomorphic to an object of `M`. -/
def EstModele {X : Mᵒᵖ ⥤ Type w} (S : Subfunctor X) : Prop :=
  ∃ D : M, Nonempty (S.toFunctor ≅ yoneda.obj D)

/-- **The admissible objects** of page 12: `X` is the supremum of its model sub-objects, and the
intersection of two model sub-objects is the supremum of the model sub-objects it contains. -/
def Admissible (X : Mᵒᵖ ⥤ Type w) : Prop :=
  sSup {S : Subfunctor X | EstModele S} = ⊤ ∧
    ∀ S T : Subfunctor X, EstModele S → EstModele T →
      S ⊓ T = sSup {R | EstModele R ∧ R ≤ S ⊓ T}

lemma nonSingulier_iff_mono (X : Mᵒᵖ ⥤ Type w) :
    NonSingulier X ↔ ∀ (D : M) (x : X.obj (op D)), Mono (yonedaEquiv.symm x) := by
  simp only [NatTrans.mono_iff_mono_app, mono_iff_injective]
  refine ⟨fun h D x U a b hab => h x a b hab, fun h D D' x a b hab => h D x (op D') hab⟩

/-- The model sub-object generated by an element of a non-singular presheaf. -/
noncomputable def modeleEngendre {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) :
    Subfunctor X :=
  Subfunctor.range (yonedaEquiv.symm x)

lemma mem_modeleEngendre {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) :
    x ∈ (modeleEngendre x).obj (op D) :=
  ⟨𝟙 D, by simp [yonedaEquiv_symm_app_apply]⟩

lemma modeleEngendre_le {X : Mᵒᵖ ⥤ Type w} {D : M} (x : X.obj (op D)) (T : Subfunctor X)
    (hx : x ∈ T.obj (op D)) : modeleEngendre x ≤ T := by
  rintro U _ ⟨a, rfl⟩
  exact T.map a.op hx

lemma estModele_modeleEngendre {X : Mᵒᵖ ⥤ Type w} (hX : NonSingulier X) {D : M}
    (x : X.obj (op D)) : EstModele (modeleEngendre x) := by
  have := (nonSingulier_iff_mono X).1 hX D x
  exact ⟨D, ⟨(asIso (Subfunctor.toRange (yonedaEquiv.symm x))).symm⟩⟩

variable (hmono : ∀ {X Y : M} (f : X ⟶ Y), Mono f)

include hmono in
/-- **Page 12, read in the presheaf language.** When every arrow of `M` is a monomorphism, a
presheaf is admissible iff it is non-singular: every element is a monomorphism `yoneda D → X`.
The first condition of page 12 alone implies it; the second then follows. -/
theorem admissible_iff (X : Mᵒᵖ ⥤ Type w) : Admissible X ↔ NonSingulier X := by
  constructor
  · rintro ⟨h1, -⟩ D D' x a b hab
    have hx : x ∈ (sSup {S : Subfunctor X | EstModele S}).obj (op D) := by rw [h1]; trivial
    simp only [Subfunctor.sSup_obj, Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_image,
      Set.mem_ofPred_eq] at hx
    obtain ⟨_, ⟨S, ⟨E, ⟨e⟩⟩, rfl⟩, hxS⟩ := hx
    let s : S.toFunctor.obj (op D) := ⟨x, hxS⟩
    have hs : S.toFunctor.map a.op s = S.toFunctor.map b.op s := Subtype.ext hab
    have na := NatTrans.naturality_apply e.hom a.op s
    have nb := NatTrans.naturality_apply e.hom b.op s
    rw [hs, nb] at na
    simp only [yoneda_obj_map, Quiver.Hom.unop_op] at na
    exact (cancel_mono (e.hom.app (op D) s)).1 na.symm
  · intro hX
    refine ⟨eq_top_iff.2 fun U x _ => ?_, fun S T _ _ => le_antisymm (fun U z hz => ?_)
      (sSup_le fun R hR => hR.2)⟩
    · exact (le_sSup (estModele_modeleEngendre hX x) : modeleEngendre x ≤ _) U
        (mem_modeleEngendre x)
    · exact (le_sSup (show modeleEngendre z ∈ {R | EstModele R ∧ R ≤ S ⊓ T} from
        ⟨estModele_modeleEngendre hX z, modeleEngendre_le z _ hz⟩)) U (mem_modeleEngendre z)

variable (hend : ∀ {X : M} (f : X ⟶ X), f = 𝟙 X) (hsk : Skeletal M)

/-- The elements of `X`, pairs `(D, x)` with `x ∈ X(D)`: in a skeletal `M`, the model
sub-objects of a non-singular `X`. -/
abbrev Elem (X : Mᵒᵖ ⥤ Type w) : Type w := Σ D : M, X.obj (op D)

include hend hsk in
lemma eq_of_aller_retour {D E : M} (a : D ⟶ E) (b : E ⟶ D) : D = E :=
  hsk ⟨⟨a, b, hend _, hend _⟩⟩

include hend hsk in
/-- The order of `X̃`: `(D', x') ≤ (D, x)` iff `x' = X(a)(x)` for an arrow `a : D' → D`. -/
@[instance_reducible]
def ordreElem (X : Mᵒᵖ ⥤ Type w) : PartialOrder (Elem X) where
  le p q := ∃ a : p.1 ⟶ q.1, X.map a.op q.2 = p.2
  le_refl p := ⟨𝟙 _, by simp⟩
  le_trans p q r := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a ≫ b, by simp [hb, ha]⟩
  le_antisymm := by
    rintro ⟨D, x⟩ ⟨E, y⟩ ⟨a, ha⟩ ⟨b, hb⟩
    dsimp at a b ha hb
    obtain rfl := eq_of_aller_retour hend hsk a b
    rw [hend a] at ha
    simp only [op_id, Functor.map_id_apply] at ha
    rw [ha]

lemma le_elem_iff (X : Mᵒᵖ ⥤ Type w) (p q : Elem X) :
    (ordreElem hend hsk X).le p q ↔ ∃ a : p.1 ⟶ q.1, X.map a.op q.2 = p.2 := Iff.rfl

/-- **The `M`-pinned poset `X̃` of a non-singular presheaf** (page 12): its elements with the
type map `(D, x) ↦ D` and the pinning `u_{(D,x)}(D', a) = (D', X(a)(x))`. -/
def versEpingleObj (X : Mᵒᵖ ⥤ Type w) (hX : NonSingulier X) : Epingle M :=
  letI := ordreElem hend hsk X
  { K := Elem X
    τ := Sigma.fst
    τ_strict := by
      rintro ⟨D, x⟩ ⟨E, y⟩ hlt
      obtain ⟨⟨a, ha⟩, hn⟩ := lt_iff_le_not_ge.1 hlt
      refine ⟨⟨a⟩, fun h => hn ?_⟩
      dsimp at h a ha
      subst h
      rw [hend a] at ha
      exact ⟨𝟙 _, by simpa using ha.symm⟩
    u := fun ξ y => ⟨y.1, X.map y.2.op ξ.2⟩
    u_top := fun ξ => by simp
    u_injective := by
      rintro ξ ⟨E, c⟩ ⟨E', c'⟩ h
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
      rw [hX ξ.2 c c' (eq_of_heq h)]
    u_range := by
      intro ξ
      ext q
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y.2, rfl⟩
      · rintro ⟨a, ha⟩
        exact ⟨⟨q.1, a⟩, by dsimp only; rw [ha]⟩
    u_le := by
      rintro ξ ⟨E, c⟩ ⟨E', c'⟩
      change (∃ w : E ⟶ E', _) ↔ ∃ w : E ⟶ E', w ≫ c' = c
      refine exists_congr fun w => ⟨fun h => hX ξ.2 _ _ ?_, fun h => ?_⟩
      · simpa using h
      · simp [← h]
    τ_u := fun _ _ => rfl
    u_u := fun ξ y z => by simp }

/-- A natural transformation gives a morphism of pinned posets, `(D, x) ↦ (D, α(x))`. -/
def versEpingleMap {X Y : Mᵒᵖ ⥤ Type w} (hX : NonSingulier X) (hY : NonSingulier Y)
    (α : X ⟶ Y) : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY where
  f p := ⟨p.1, α.app _ p.2⟩
  strictMono := by
    rintro ⟨D, x⟩ ⟨E, y⟩ hlt
    obtain ⟨⟨a, ha⟩, hn⟩ := lt_iff_le_not_ge.1 hlt
    refine lt_iff_le_not_ge.2
      ⟨⟨a, by rw [← NatTrans.naturality_apply]; exact congrArg _ ha⟩, fun ⟨b, hb⟩ => hn ?_⟩
    dsimp at a b ha hb
    obtain rfl := eq_of_aller_retour hend hsk a b
    rw [hend a] at ha
    exact ⟨𝟙 _, by simpa using ha.symm⟩
  τ_f _ := rfl
  u_f := by
    rintro ⟨D, x⟩ ⟨E, (c : E ⟶ D)⟩
    change (⟨E, α.app _ (X.map c.op x)⟩ : Elem Y) = ⟨E, Y.map (c ≫ 𝟙 D).op (α.app _ x)⟩
    rw [Category.comp_id, NatTrans.naturality_apply]

/-- The category `𝔹₀` of admissible presheaves, a full subcategory of `M̂`. -/
abbrev Adm (M : Type w) [SmallCategory M] :=
  ObjectProperty.FullSubcategory (Admissible (M := M))

include hmono in
/-- **The functor `X ↦ X̃`** from admissible presheaves to `M`-pinned posets. -/
def versEpingle : Adm M ⥤ Epingle M where
  obj X := versEpingleObj hend hsk X.obj ((admissible_iff hmono _).1 X.property)
  map α := versEpingleMap hend hsk _ _ α.hom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

lemma elem_eq_transport {X : Mᵒᵖ ⥤ Type w} {D : M} (q : Elem X) (h : q.1 = D) :
    q = ⟨D, X.map (eqToHom h.symm).op q.2⟩ := by
  obtain ⟨E, y⟩ := q
  subst h
  simp

/-- The component at `D` of the natural transformation a morphism of pinned posets comes from. -/
def appOfHom {X Y : Mᵒᵖ ⥤ Type w} {hX : NonSingulier X} {hY : NonSingulier Y}
    (φ : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY) (D : M)
    (x : X.obj (op D)) : Y.obj (op D) :=
  Y.map (eqToHom (φ.τ_f ⟨D, x⟩).symm).op (φ.f ⟨D, x⟩).2

lemma f_eq_appOfHom {X Y : Mᵒᵖ ⥤ Type w} {hX : NonSingulier X} {hY : NonSingulier Y}
    (φ : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY) (p : Elem X) :
    φ.f p = ⟨p.1, appOfHom hend hsk φ p.1 p.2⟩ :=
  elem_eq_transport _ (φ.τ_f p)

lemma appOfHom_naturality {X Y : Mᵒᵖ ⥤ Type w} {hX : NonSingulier X} {hY : NonSingulier Y}
    (φ : versEpingleObj hend hsk X hX ⟶ versEpingleObj hend hsk Y hY) {D D' : M}
    (a : D' ⟶ D) (x : X.obj (op D)) :
    appOfHom hend hsk φ D' (X.map a.op x) = Y.map a.op (appOfHom hend hsk φ D x) := by
  have h := φ.u_f ⟨D, x⟩ ⟨D', a⟩
  change φ.f ⟨D', X.map a.op x⟩ = ⟨D', Y.map (a ≫ eqToHom _).op (φ.f ⟨D, x⟩).2⟩ at h
  rw [f_eq_appOfHom] at h
  obtain ⟨-, h⟩ := Sigma.mk.inj_iff.1 h
  rw [eq_of_heq h, appOfHom, op_comp, Functor.map_comp_apply]
  rfl

include hmono in
instance : (versEpingle hmono hend hsk).Faithful where
  map_injective {X Y α β} h := by
    ext U x
    have := congrFun (congrArg Epingle.Hom.f h) ⟨U.unop, x⟩
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2

include hmono in
instance : (versEpingle hmono hend hsk).Full where
  map_surjective {X Y} φ := by
    refine ⟨ObjectProperty.homMk
      { app := fun U => TypeCat.ofHom (appOfHom hend hsk
          (hX := (admissible_iff hmono _).1 X.property)
          (hY := (admissible_iff hmono _).1 Y.property) φ U.unop)
        naturality := fun U V g => by
          ext x
          exact appOfHom_naturality hend hsk φ g.unop x }, ?_⟩
    ext p
    exact (f_eq_appOfHom hend hsk φ p).symm

/-- **The presheaf of an `M`-pinned poset**: `X_K(D)` is the set of elements of type `D`, and
`a : D' → D` acts by the pinning, `ξ ↦ u_ξ(D', a)`. -/
def versPrefaisceau (K : Epingle M) : Mᵒᵖ ⥤ Type w where
  obj U := {ξ : K.K // K.τ ξ = U.unop}
  map {U V} g := TypeCat.ofHom fun ξ =>
    ⟨K.u ξ.1 ⟨V.unop, g.unop ≫ eqToHom ξ.2.symm⟩, K.τ_u _ _⟩
  map_id U := by
    ext ⟨ξ, h⟩
    change K.u ξ ⟨U.unop, 𝟙 _ ≫ eqToHom h.symm⟩ = ξ
    obtain ⟨D⟩ := U
    dsimp at h ⊢
    subst h
    simpa using K.u_top ξ
  map_comp {U V W} g g' := by
    ext ⟨ξ, h⟩
    change K.u ξ ⟨W.unop, (g'.unop ≫ g.unop) ≫ eqToHom h.symm⟩ =
      K.u (K.u ξ ⟨V.unop, g.unop ≫ eqToHom h.symm⟩) ⟨W.unop,
        g'.unop ≫ eqToHom (K.τ_u ξ ⟨V.unop, g.unop ≫ eqToHom h.symm⟩).symm⟩
    rw [K.u_u ξ ⟨V.unop, g.unop ≫ eqToHom h.symm⟩ ⟨W.unop, g'.unop⟩, Category.assoc]

lemma versPrefaisceau_nonSingulier (K : Epingle M) : NonSingulier (versPrefaisceau K) := by
  rintro D D' ⟨ξ, h⟩ a b hab
  have := K.u_injective ξ (congrArg Subtype.val hab)
  obtain ⟨-, h'⟩ := Sigma.mk.inj_iff.1 this
  exact (cancel_mono _).1 (eq_of_heq h')

lemma versPrefaisceau_le_iff (K : Epingle M) (p q : Elem (versPrefaisceau K)) :
    (ordreElem hend hsk _).le p q ↔ p.2.1 ≤ q.2.1 := by
  obtain ⟨D, ξ, hξ⟩ := p
  obtain ⟨E, η, hη⟩ := q
  dsimp at hξ hη ⊢
  rw [le_elem_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h1 : K.u η ⟨D, a ≫ eqToHom hη.symm⟩ = ξ := congrArg Subtype.val ha
    rw [← h1, ← Set.mem_Iic, ← K.u_range]
    exact ⟨_, rfl⟩
  · intro hle
    rw [← Set.mem_Iic, ← K.u_range] at hle
    obtain ⟨⟨F, c⟩, hc⟩ := hle
    have hF : F = D := by
      have := K.τ_u η ⟨F, c⟩
      rw [hc] at this
      exact this.symm.trans hξ
    subst hF hξ hη
    refine ⟨c, Subtype.ext ?_⟩
    change K.u η ⟨_, c ≫ 𝟙 _⟩ = ξ
    rw [Category.comp_id, hc]

lemma versPrefaisceau_mk_eq (K : Epingle M) (ζ : K.K) (D : M) (h : K.τ ζ = D) :
    (⟨K.τ ζ, ζ, rfl⟩ : Elem (versPrefaisceau K)) = ⟨D, ζ, h⟩ := by
  subst h
  rfl

/-- `X_K` gives back `K`: the pinned poset of the presheaf of `K` is isomorphic to `K`. -/
def isoVersPrefaisceau (K : Epingle M) :
    versEpingleObj hend hsk (versPrefaisceau K) (versPrefaisceau_nonSingulier K) ≅ K where
  hom :=
    { f := fun p => p.2.1
      strictMono := fun p q hpq => by
        obtain ⟨h1, h2⟩ := lt_iff_le_not_ge.1 hpq
        exact lt_iff_le_not_ge.2 ⟨(versPrefaisceau_le_iff hend hsk K p q).1 h1,
          fun h => h2 ((versPrefaisceau_le_iff hend hsk K q p).2 h)⟩
      τ_f := fun p => p.2.2
      u_f := fun _ _ => rfl }
  inv :=
    { f := fun ξ => ⟨K.τ ξ, ξ, rfl⟩
      strictMono := fun ξ η hξη => by
        obtain ⟨h1, h2⟩ := lt_iff_le_not_ge.1 hξη
        exact lt_iff_le_not_ge.2 ⟨(versPrefaisceau_le_iff hend hsk K _ _).2 h1,
          fun h => h2 ((versPrefaisceau_le_iff hend hsk K _ _).1 h)⟩
      τ_f := fun _ => rfl
      u_f := fun ξ y => by
        rw [versPrefaisceau_mk_eq K (K.u ξ y) y.1 (K.τ_u ξ y)]
        refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
        change K.u ξ y = K.u ξ ⟨y.1, (y.2 ≫ eqToHom _) ≫ eqToHom _⟩
        simp }
  hom_inv_id := by
    ext ⟨D, ξ, h⟩
    exact versPrefaisceau_mk_eq K ξ D h
  inv_hom_id := rfl

include hmono in
instance : (versEpingle hmono hend hsk).EssSurj where
  mem_essImage K :=
    ⟨⟨versPrefaisceau K, (admissible_iff hmono _).2 (versPrefaisceau_nonSingulier K)⟩,
      ⟨isoVersPrefaisceau hend hsk K⟩⟩

include hmono in
/-- **Page 13, « est équivalente à ».** For a skeletal `M` satisfying (i) and (ii), `X ↦ X̃` is
an equivalence between the admissible presheaves on `M` and the `M`-pinned posets. -/
theorem versEpingle_isEquivalence : (versEpingle hmono hend hsk).IsEquivalence := by
  sorry

end Prefaisceaux

end Grothendieck.Folder104
