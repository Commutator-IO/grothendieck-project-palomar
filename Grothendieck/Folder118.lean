module

public import Mathlib

@[expose] public section


/-!
# Folder 118, page 35: stability of `𝒲_A` under products without asphericity

The modernised reading `transcripts/118/118.modern.tex` (« Le lemme des pages 32 à 35 »)
shows that for a small category `A`, (i) « `A` totally aspherical » is equivalent to (ii)
« `𝒲_A` stable under finite products » plus « `A` aspherical », and asks on page 35
whether a connected `A` satisfying (ii) must be aspherical. The page answers « Non »:
for `A` a groupoid, `𝒲_A` consists of the isomorphisms only (for the usual weak
equivalences), hence is stable under finite products, while `A` is not aspherical. The
reading takes `A = BG` connected with `G ≠ 1`. This is the reachable part of finding
`118-groupoid-products-not-totally-aspherical` of `src/content/findings.ts`.

What is formalised, in a 1-truncated model. Presheaves on `BG` are `G`-sets, and for a
`G`-set `X` the category `A/X` is the action groupoid `X//G`. A functor between groupoids
is a weak equivalence (of nerves) iff it is bijective on connected components and an
isomorphism on automorphism groups; for the functor `X//G → Y//G` induced by a map `f` of
`G`-sets, this says that `f` is bijective on orbits and `Stab(f x) = Stab(x)`. That
characterisation of weak equivalences of groupoids is taken as the definition (`IsWeq`), not
proved; similarly `X//G` is aspherical iff it is connected with trivial automorphism groups
(`Aspherical`).

* `isWeq_iff_bijective`: `f ∈ 𝒲_A` iff `f` is bijective — the reading's reason
  (« a map of `G`-sets bijective on orbits and an isomorphism on stabilisers is an
  isomorphism »), and its converse.
* `isWeq_prod`, `isWeq_pi`: `𝒲_A` is stable under binary products and under products of
  any family, finite or not.
* `not_aspherical_point`, `not_aspherical_regular_prod`: for `G ≠ 1`, `A = A/e` is not
  aspherical, nor is `a × a` for the representable `a` (the regular `G`-set).
* `answer_page_35`: the three together.
-/

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

/-- **Page 35**: for `A = BG`, `𝒲_A` consists of the isomorphisms. -/
theorem isWeq_iff_bijective {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) :
    IsWeq G f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨hs, hi, hst⟩
    refine ⟨fun x x' hxx => ?_, fun y => ?_⟩
    · obtain ⟨h, rfl⟩ := hi x x' 1 (by rw [one_smul, hxx])
      rw [hst x h (by rw [← map_smul, hxx])]
    · obtain ⟨x, g, rfl⟩ := hs y
      exact ⟨g • x, map_smul f g x⟩
  · rintro ⟨hinj, hsurj⟩
    exact ⟨fun y => (hsurj y).imp fun x hx => ⟨1, by rw [one_smul, hx]⟩,
      fun x x' g hg => ⟨g, hinj (by rw [map_smul, hg])⟩,
      fun x g hg => hinj (by rw [map_smul, hg])⟩

/-- The product of two maps of `G`-sets. -/
def prodHom {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] (f : X →[G] Y) (f' : X' →[G] Y') : X × X' →[G] Y × Y' where
  toFun p := (f p.1, f' p.2)
  map_smul' g p := by simp [map_smul]

/-- `𝒲_A` is stable under binary products (condition (ii)). -/
theorem isWeq_prod {X Y X' Y' : Type*} [MulAction G X] [MulAction G Y] [MulAction G X']
    [MulAction G Y'] {f : X →[G] Y} {f' : X' →[G] Y'} (hf : IsWeq G f) (hf' : IsWeq G f') :
    IsWeq G (prodHom f f') := by
  rw [isWeq_iff_bijective] at *
  exact hf.prodMap hf'

/-- The product of a family of maps of `G`-sets. -/
def piHom {ι : Type*} {X Y : ι → Type*} [∀ i, MulAction G (X i)] [∀ i, MulAction G (Y i)]
    (f : ∀ i, X i →[G] Y i) : (∀ i, X i) →[G] (∀ i, Y i) where
  toFun x i := f i (x i)
  map_smul' g x := by funext i; simp [map_smul]

/-- `𝒲_A` is stable under products of any family, finite or not. -/
theorem isWeq_pi {ι : Type*} {X Y : ι → Type*} [∀ i, MulAction G (X i)]
    [∀ i, MulAction G (Y i)] {f : ∀ i, X i →[G] Y i} (hf : ∀ i, IsWeq G (f i)) :
    IsWeq G (piHom f) :=
  (isWeq_iff_bijective _).2 (.piMap fun i => (isWeq_iff_bijective _).1 (hf i))

/-- `A = A/e` is not aspherical when `G ≠ 1`. -/
theorem not_aspherical_point [Nontrivial G] : ¬ Aspherical G PUnit := by
  rintro ⟨-, -, h⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact hg (h PUnit.unit g rfl)

/-- `a × a` is not aspherical for the representable `a`, the regular `G`-set, when
`G ≠ 1`: `(1, 1)` and `(1, g)` lie in different orbits. -/
theorem not_aspherical_regular_prod [Nontrivial G] : ¬ Aspherical G (G × G) := by
  rintro ⟨-, h, -⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨g, hg⟩ := h (1, 1) (1, a)
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at hg
  exact ha (hg.2.symm.trans hg.1)

/-- **The answer « Non » of page 35**, for `A = BG`, `G ≠ 1`: `𝒲_A` is stable under
products, but neither `A` nor `a × a` is aspherical. -/
theorem answer_page_35 [Nontrivial G] :
    (∀ {X Y X' Y' : Type} [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
      (f : X →[G] Y) (f' : X' →[G] Y'), IsWeq G f → IsWeq G f' → IsWeq G (prodHom f f')) ∧
    ¬ Aspherical G PUnit ∧ ¬ Aspherical G (G × G) :=
  ⟨fun _ _ hf hf' => isWeq_prod hf hf', not_aspherical_point, not_aspherical_regular_prod⟩

/-! ### Cisinski, Astérisque 308, Proposition 4.3.2: (g) does not imply (c)

The comparison of this section with Cisinski's book is the edition's, not the page's.
Cisinski (*Les préfaisceaux comme modèles des types d'homotopie*, Astérisque 308, 2006,
doi:10.24033/ast.715), Proposition 4.3.2, lists conditions on a small category `A` claimed
equivalent, among them (c): for presheaves `X`, `Y` on `A`, the canonical functor
`A/(X × Y) → A/X × A/Y` is a weak equivalence, and (g): `𝒲_A` is stable under finite
products. For `A = BG`, `G ≠ 1`, (g)
holds (`condition_g_holds`) and (c) fails (`not_condition_c`; witnesses
`not_isWeqOver_regular`, `not_isWeqOver_point`), so (g) does not imply (c) (`g_not_imp_c`).
Cisinski confirmed on MathOverflow (https://mathoverflow.net/questions/516223, answer of
21 October 2026) that (g) ⇒ (c) needs a further assumption, e.g. that `A` be a test category.

Same 1-truncated model as above. A functor of action groupoids `X//G → Y//H` is given by a
group morphism `φ : G →* H` and a map `f : X → Y` with `f (g • x) = φ g • f x`; it is a weak
equivalence (`IsWeqOver`) iff it is bijective on orbits and `Stab(x) → Stab(f x)`, `g ↦ φ g`,
is bijective — again a definition, not proved from nerves. `A/X × A/Y` is the action
groupoid of `G × G` on `ExtProd X Y = X × Y`, and the canonical functor is
`(X × Y)//G → (X × Y)//(G × G)`, `(x, y) ↦ (x, y)`, `g ↦ (g, g)`. The direction (c) ⇒ (g),
which Cisinski keeps, holds in the model only because (g) always does (`condition_g_of_c`).
-/

section Cisinski

universe u

/-- A functor `X//G → Y//H` given by `φ` and `f` is a weak equivalence, read 1-truncated:
surjective and injective on orbits, surjective and injective on automorphism groups. -/
def IsWeqOver {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (φ : G →* H) (f : X → Y) : Prop :=
  (∀ y : Y, ∃ (x : X) (h : H), h • f x = y) ∧
  (∀ (x x' : X) (h : H), h • f x = f x' → ∃ g : G, g • x = x') ∧
  (∀ (x : X) (h : H), h • f x = f x → ∃ g : G, g • x = x ∧ φ g = h) ∧
  (∀ (x : X) (g : G), g • x = x → φ g = 1 → g = 1)

/-- Over the identity of `G`, `IsWeqOver` is `IsWeq`. -/
theorem isWeqOver_id_iff {X Y : Type*} [MulAction G X] [MulAction G Y] (f : X →[G] Y) :
    IsWeqOver (MonoidHom.id G) f ↔ IsWeq G f := by
  simp only [IsWeqOver, IsWeq, MonoidHom.id_apply, exists_eq_right]
  exact ⟨fun ⟨h₁, h₂, h₃, _⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃, fun _ _ _ => id⟩⟩

/-- `X × Y` with `G × H` acting factorwise: the objects of `X//G × Y//H`. -/
def ExtProd (X Y : Type*) : Type _ := X × Y

instance {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y] :
    MulAction (G × H) (ExtProd X Y) where
  smul g p := ((g.1 • p.1 : X), (g.2 • p.2 : Y))
  one_smul p := Prod.ext (one_smul G p.1) (one_smul H p.2)
  mul_smul g g' p := Prod.ext (mul_smul g.1 g'.1 p.1) (mul_smul g.2 g'.2 p.2)

theorem extProd_smul {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]
    (g : G × H) (p : ExtProd X Y) : g • p = ((g.1 • p.1 : X), (g.2 • p.2 : Y)) := rfl

/-- The diagonal `G →* G × G`, on arrows of `A/(X × Y) → A/X × A/Y`. -/
abbrev diagHom (G : Type*) [Group G] : G →* G × G := (MonoidHom.id G).prod (MonoidHom.id G)

/-- The canonical functor `A/(X × Y) → A/X × A/Y` for `A = BG`, on objects. -/
def canonical (X Y : Type*) : X × Y → ExtProd X Y := id

/-- Condition (c) of Cisinski's Proposition 4.3.2 for `A = BG`, in the model. -/
def condition_c (G : Type u) [Group G] : Prop :=
  ∀ (X Y : Type u) [MulAction G X] [MulAction G Y], IsWeqOver (diagHom G) (canonical X Y)

/-- Condition (g) of Cisinski's Proposition 4.3.2 for `A = BG`, in the model. -/
def condition_g (G : Type u) [Group G] : Prop :=
  ∀ (X Y X' Y' : Type u) [MulAction G X] [MulAction G Y] [MulAction G X'] [MulAction G Y']
    (f : X →[G] Y) (f' : X' →[G] Y'), IsWeq G f → IsWeq G f' → IsWeq G (prodHom f f')

/-- (g) holds for `A = BG`: `isWeq_prod`. -/
theorem condition_g_holds (G : Type u) [Group G] : condition_g G :=
  fun _ _ _ _ _ _ _ _ _ _ => isWeq_prod

/-- (c) ⇒ (g) in the model, only because (g) always holds there. -/
theorem condition_g_of_c {G : Type u} [Group G] (_ : condition_c G) : condition_g G :=
  condition_g_holds G

/-- For `X = Y = a` the regular `G`-set and `G ≠ 1`, the canonical functor
`(G × G)//G → G//G × G//G` is not a weak equivalence: `(1, 1)` and `(1, a)`, `a ≠ 1`, lie in
one component of the target (which is a point) but in two components of the source (which
has one per element of `G`, the orbit of `(g, h)` being labelled by `g⁻¹ h`). -/
theorem not_isWeqOver_regular [Nontrivial G] : ¬ IsWeqOver (diagHom G) (canonical G G) := by
  rintro ⟨-, h, -⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨g, hg⟩ := h (1, 1) (1, a) (1, a) (Prod.ext (mul_one 1) (mul_one a))
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq] at hg
  exact ha (hg.2.symm.trans hg.1)

/-- For `X = Y = e` the terminal `G`-set and `G ≠ 1`, the canonical functor `BG → BG × BG`
is not a weak equivalence: the diagonal `G → G × G` misses `(1, a)`, `a ≠ 1`. -/
theorem not_isWeqOver_point [Nontrivial G] :
    ¬ IsWeqOver (diagHom G) (canonical PUnit PUnit) := by
  rintro ⟨-, -, h, -⟩
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  obtain ⟨g, -, hg⟩ := h (PUnit.unit, PUnit.unit) (1, a) rfl
  simp only [MonoidHom.prod_apply, MonoidHom.id_apply, Prod.mk.injEq] at hg
  exact ha (hg.2.symm.trans hg.1)

/-- (c) fails for `A = BG`, `G ≠ 1`. -/
theorem not_condition_c (G : Type u) [Group G] [Nontrivial G] : ¬ condition_c G :=
  fun h => not_isWeqOver_regular (h G G)

/-- (c) holds for `A = BG` exactly when `G` is trivial. -/
theorem condition_c_iff_subsingleton (G : Type u) [Group G] :
    condition_c G ↔ Subsingleton G := by
  refine ⟨fun h => not_nontrivial_iff_subsingleton.1 fun _ => not_condition_c G h,
    fun _ X Y _ _ => ⟨fun y => ⟨y, 1, one_smul _ _⟩, fun x x' k hk => ⟨1, ?_⟩,
      fun x k _ => ⟨1, one_smul _ _, Subsingleton.elim _ _⟩, fun _ g _ _ => Subsingleton.elim _ _⟩⟩
  rw [one_smul]; rwa [Subsingleton.elim k 1, one_smul] at hk

/-- **Cisinski, Proposition 4.3.2, (g) ⇏ (c)**, for `A = BG`, `G ≠ 1`, in the model: `𝒲_A`
is stable under finite products, while `A/(X × Y) → A/X × A/Y` is not always a weak
equivalence. -/
theorem g_not_imp_c (G : Type u) [Group G] [Nontrivial G] :
    condition_g G ∧ ¬ condition_c G :=
  ⟨condition_g_holds G, not_condition_c G⟩

end Cisinski

/-! ### Page 35: condition (iv) is not stable under sums

The page says (iv) is « visiblement stable par sommes (i.e. si des `A_α` y satisfont,
`∐ A_α` aussi), mais la condition (i) non ». The second reading of the edition corrects this:
for `a`, `b` in two different summands, `a × b` is the empty presheaf, `A_{/a × b}` is the
empty category, and the empty category is not aspherical. So (iv) is not stable under sums,
and, for `A` non-empty, (iv) already forces `A` to be connected.

Here `A` is any small category of mathlib and `a × b` is the presheaf
`c ↦ Hom(c, a) × Hom(c, b)` (`FunctorToTypes.prod` of the two representables, the product in
`Â`). `A_{/X}` is the category of elements `X.Elements` (mathlib orients its arrows the other
way, which changes neither emptiness nor connectedness). Asphericity of a category (its nerve
weakly contractible) is not defined here: only its consequence « non-empty and connected »
(`π₀` of the nerve is the set of components) is used, as `IsConnected`. So `ConnectedProducts A`
is a consequence of (iv), « `A_{/a × b}` aspherical for all `a`, `b` », and its failure is the
failure of (iv) for any notion of asphericity that includes connectedness, among them the
1-truncated one above.
-/

section Sums

open CategoryTheory

/-- The presheaf `a × b` on `A`, product of the representables `a` and `b`. -/
abbrev prodRep {A : Type*} [Category A] (a b : A) : Aᵒᵖ ⥤ Type _ :=
  FunctorToTypes.prod (yoneda.obj a) (yoneda.obj b)

/-- The connectedness part of (iv): `A_{/a × b}` is non-empty and connected for all `a`, `b`. -/
def ConnectedProducts (A : Type*) [Category A] : Prop :=
  ∀ a b : A, IsConnected (prodRep a b).Elements

/-- For `a ∈ A₁`, `b ∈ A₂`, `A_{/a × b}` is empty in `A₁ ⊔ A₂`: no `c` maps to both. -/
theorem isEmpty_elements_sum {A₁ A₂ : Type*} [Category A₁] [Category A₂] (a : A₁) (b : A₂) :
    IsEmpty (prodRep (Sum.inl a : A₁ ⊕ A₂) (Sum.inr b)).Elements := by
  refine ⟨fun x => ?_⟩
  rcases x with @⟨⟨_ | _⟩, f, g⟩
  exacts [hom_inl_inr_false A₁ A₂ (Y := b) g, hom_inr_inl_false A₂ A₁ (Y := a) f]

/-- The empty category is not connected, hence not aspherical. -/
theorem not_isConnected_of_isEmpty (C : Type*) [Category C] [IsEmpty C] : ¬ IsConnected C :=
  fun h => isEmptyElim h.is_nonempty.some

/-- (iv) fails for a sum of two non-empty categories. -/
theorem not_connectedProducts_sum {A₁ A₂ : Type*} [Category A₁] [Category A₂] [Nonempty A₁]
    [Nonempty A₂] : ¬ ConnectedProducts (A₁ ⊕ A₂) := fun h =>
  @not_isConnected_of_isEmpty _ _ (isEmpty_elements_sum (Classical.arbitrary A₁)
    (Classical.arbitrary A₂)) (h _ _)

/-- The point satisfies (iv): `A_{/e × e}` is the point. -/
theorem connectedProducts_point : ConnectedProducts (Discrete PUnit) := by
  rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
  have : Nonempty (prodRep (A := Discrete PUnit) ⟨⟨⟩⟩ ⟨⟨⟩⟩).Elements :=
    ⟨Functor.elementsMk _ (Opposite.op ⟨⟨⟩⟩) (𝟙 _, 𝟙 _)⟩
  refine zigzag_isConnected fun x y => ?_
  rcases x with @⟨⟨⟨⟨⟩⟩⟩, ⟨⟨_⟩⟩, ⟨⟨_⟩⟩⟩
  rcases y with @⟨⟨⟨⟨⟩⟩⟩, ⟨⟨_⟩⟩, ⟨⟨_⟩⟩⟩
  rfl

/-- **Page 35, corrected**: (iv) is not stable under sums — the point satisfies it, the sum of
two points does not. -/
theorem connectedProducts_not_stable_under_sums :
    ConnectedProducts (Discrete PUnit) ∧ ¬ ConnectedProducts (Discrete PUnit ⊕ Discrete PUnit) :=
  ⟨connectedProducts_point, not_connectedProducts_sum⟩

/-- (iv) forces a non-empty `A` to be connected: an object of `A_{/a × b}` is a span
`a ← c → b`. -/
theorem isConnected_of_connectedProducts {A : Type*} [Category A] [Nonempty A]
    (h : ConnectedProducts A) : IsConnected A :=
  zigzag_isConnected fun a b => by
    obtain @⟨⟨c⟩, f, g⟩ := (h a b).is_nonempty.some
    exact Zigzag.of_inv_hom f g

end Sums

end Grothendieck.Folder118
