module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Filtration
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Category.Cat
public import Grothendieck.Upstream.PrimaryComponentInjective

@[expose] public section


/-!
# Folder 21, Proposition 2.15 and Corollaire 2.16: `I`-torsion and injectivity

The modernised reading `transcripts/21/21.modern.tex` (typescript pages 11–13)
states, for `A` a commutative Noetherian ring and `I` an ideal:

> **Proposition 2.15.** Avec les notations précédentes, pour que `H` soit un
> `A`-module injectif, il faut et il suffit que le foncteur
> `T_H(M) = Hom(M,H)` sur la catégorie `𝒞` des `A`-modules de type fini annulés
> par une puissance de `I` soit exact à droite, donc exact.
>
> La nécessité est triviale. Pour la suffisance, il suffit — c'est le critère
> de Baer — de vérifier que pour tout sous-module `N` de `A`, l'application
> `Hom(A,H) → Hom(N,H)` est surjective … Soit donc `u : N → H`. Son image est un
> sous-module de type fini de `H`, donc annulé par une puissance de `I` : `u`
> est nul sur `IⁿN`. Par le lemme d'Artin–Rees, il existe `m` tel que
> `N ∩ IᵐM ⊂ IⁿN`. …
>
> **Corollaire 2.16.** Soit `K` un `A`-module et soit `H⁰_I(K)` le sous-module
> des éléments annulés par une puissance de `I`. Si `K` est injectif, `H⁰_I(K)`
> l'est aussi.

Here `H` is, as « avec les notations précédentes » says (2.9, 2.14), an
`A`-module every element of which is killed by a power of `I`. "`Hom(-,H)` exact
à droite on `𝒞`" is: for every `M ∈ 𝒞` and every submodule `N ⊆ M`, every
`N → H` extends to `M` (`ExactSurC`).

What is proved, as the reading states it:

* `proposition2_15` — for `A` Noetherian and `H` of `I`-power torsion,
  `H` injective ⟺ `Hom(-,H)` exact on `𝒞`. The proof is the typescript's:
  Baer's criterion, the image of `u` killed by one power `Iⁿ`, Artin–Rees in
  the form `N ∩ I^{n+k} ⊆ IⁿN`, and the extension along `N/(N ∩ Iᵐ) ↪ A/Iᵐ`; that
  argument is `Ideal.injective_of_primaryComponent_eq_top` (`Upstream/`).
* `corollaire2_16` — `Γ_I` preserves injectives over a Noetherian ring.

The bulk of the folder (2.1–2.14: abelian categories, cohomological functors,
Eilenberg–Watts, associated primes of the representing module; the sheaf half,
pp. 15–20; Corollaire 10 and the torsors of pp. 27–28) is not formalised here.
Proposition 7 and Corollaire 8 (pp. 21–26, fibered categories) are, in the
`Grothendieck.Folder21.Stack` namespace below.

**What the formalisation finds.** Nothing false. The Artin–Rees containment
the proof needs is `N ∩ IᵐA ⊆ IⁿN`, with the ambient module on the left — the
reading's correction of the page (the page writes `N ∩ IᵐN`, for which the
containment is trivially true for `m ⩾ n` and useless). Two small observations:
the hypothesis "`M` of finite type" on the test objects is used only through the
cyclic modules `A/Iᵐ`, so the criterion already holds when `Hom(-,H)` is only
known to be exact on inclusions `N ↪ A/Iᵐ`; and the argument of 2.16 uses no
finiteness of `M` — an extension to `M` of a map into `K` lands in `H⁰_I(K)` as
soon as `M` is killed by a power of `I` — so its Noetherian hypothesis is there
only to invoke 2.15 (Artin–Rees).

What this certifies is that the reading holds together at these points, not
that it is what the pages say (issue #26).
-/

namespace Grothendieck.Folder21

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- `M` is killed by a power of `I`. -/
def TueParPuissance (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ x : M, a • x = 0

/-- Every element of `H` is killed by some power of `I`. -/
def TorsionI (H : Type*) [AddCommGroup H] [Module A H] : Prop :=
  ∀ x : H, ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0

/-- `Hom(-,H)` is right exact on the category `𝒞` of finitely generated modules
killed by a power of `I`: maps into `H` extend along every inclusion `N ⊆ M` in
`𝒞`. -/
def ExactSurC (H : Type u) [AddCommGroup H] [Module A H] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.Finite A M → TueParPuissance I M →
    ∀ (N : Submodule A M) (f : N →ₗ[A] H), ∃ w : M →ₗ[A] H, ∀ x : N, w x = f x

/-- `H⁰_I(K)`, the elements of `K` killed by a power of `I`. -/
def gammaI (K : Type*) [AddCommGroup K] [Module A K] : Submodule A K where
  carrier := {x | ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0}
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, fun a ha => ?_⟩
    rw [smul_add, hn a (Ideal.pow_le_pow_right (le_max_left n m) ha),
      hm a (Ideal.pow_le_pow_right (le_max_right n m) ha), add_zero]
  zero_mem' := ⟨0, fun a _ => smul_zero a⟩
  smul_mem' := by
    rintro c x ⟨n, hn⟩
    exact ⟨n, fun a ha => by rw [smul_comm, hn a ha, smul_zero]⟩

/-- **Proposition 2.15.** Over a Noetherian ring, an `I`-power-torsion module `H`
is injective if and only if `Hom(-,H)` is right exact on `𝒞`. -/
theorem proposition2_15 [IsNoetherianRing A] (H : Type u) [AddCommGroup H] [Module A H]
    (hH : TorsionI I H) : Module.Injective A H ↔ ExactSurC I H := by
  constructor
  · -- La nécessité est triviale.
    exact fun hinj M _ _ _ _ N f => hinj.out N.subtype N.injective_subtype f
  · -- `H = Γ_I(H)`, and `A ⧸ Iⁿ` is in `𝒞` (`Ideal.injective_of_primaryComponent_eq_top`).
    intro hC
    refine Ideal.injective_of_primaryComponent_eq_top I (eq_top_iff.2 fun x _ => ?_)
      fun n N f => ?_
    · obtain ⟨n, hn⟩ := hH x
      exact (Ideal.primaryComponent_mem H I x).2
        ⟨n, (Submodule.mem_torsionBySet_iff _ _).2 fun a => hn a a.2⟩
    · refine hC (A ⧸ I ^ n) inferInstance ⟨n, fun a ha x => ?_⟩ N f
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right b _ ha

/-- **Corollaire 2.16.** Over a Noetherian ring, if `K` is injective then so is
`H⁰_I(K)`. -/
theorem corollaire2_16 [IsNoetherianRing A] (K : Type u) [AddCommGroup K] [Module A K]
    [hK : Module.Injective A K] : Module.Injective A (gammaI I K) := by
  rw [proposition2_15 I _ fun x => x.2.imp fun n hn a ha => Subtype.ext (hn a ha)]
  intro M _ _ _ ⟨n, hn⟩ N f
  obtain ⟨v, hv⟩ := hK.out N.subtype N.injective_subtype ((gammaI I K).subtype ∘ₗ f)
  -- The extension lands in `H⁰_I(K)`, because `M` is killed by `Iⁿ`.
  let w : M →ₗ[A] gammaI I K :=
    v.codRestrict (gammaI I K) fun x => ⟨n, fun a ha => by rw [← map_smul, hn a ha, map_zero]⟩
  exact ⟨w, fun x => Subtype.ext (hv x)⟩

end Grothendieck.Folder21

/-!
# Folder 21, pages 21–26: the pointwise criterion for a fibered category (Proposition 7)

The reading states (Définition 6, p. 21): for `Y` closed in `X`, `U = X - Y`, a fibered
category `𝓕` over the opens of `X` satisfies `(P₁)`, resp. `(P₂)`, resp. `(P₃)`, relative to
`Y` if for every open `V` the restriction `𝓕(V) ⥤ 𝓕(V ∩ U)` is faithful, resp. fully
faithful, resp. an equivalence; and it satisfies the condition at `x` if
`Pseudolim_W 𝓕(W) ⥤ Pseudolim_W 𝓕(W - W ∩ cl{x})` is so, `W` running over the open
neighbourhoods of `x`.

> **Proposition 7.** Soient `X` un espace topologique noethérien spectral, `𝓕` une catégorie
> fibrée sur la catégorie des ouverts de `X`, et `Y` une partie fermée. Sont équivalentes :
> (i) `𝓕` satisfait `(P₁)`, resp. `(P₂)`, resp. `(P₃)`, relativement à `Y` ;
> (ii) pour tout `x ∈ Y`, `𝓕` satisfait `(P₁)`, resp. `(P₂)`, resp. `(P₃)`, en `x`.
>
> **Corollaire 8.** Si `𝓕` satisfait `(P₁)`, resp. `(P₂)`, resp. `(P₃)`, relativement à `Y`,
> alors … la même condition relativement à `Y′ ⊂ Y`.

The proof of (ii) ⟹ (i) for `(P₃)` (pp. 25–26) glues an object over a neighbourhood `W` of a
maximal point of `Y` with one over `U`; the reading adds that `𝓕` must be a stack.

Model. A fibered category is a split one, a functor `(Opens X)ᵒᵖ ⥤ Cat` (every fibered
category is equivalent to a split one; that is not formalised). The 2-colimits are not
built: the conditions at `x` are their unfolded meaning (`FaithfulAt`, `FullAt`,
`EssSurjAt`: germs of morphisms and objects near `x`, off `cl{x}`). The stack hypothesis is
asked only for covers by two opens (`IsBinaryPrestack`, `IsBinaryStack`; the glued object is
not required to be compatible with the gluing isomorphism). Opens are written `T` with
`(T : Set X) = V \ Y` rather than as `V ⊓ U`, to avoid identities between opens.

What is proved:

* `proposition7_P1`, `proposition7_P2` (binary prestack) and `proposition7_P3` (binary stack),
  for `X` noetherian and quasi-sober (noetherian spectral spaces are);
* `corollaire8_P1`, `corollaire8_P2`, `corollaire8_P3`, for `Y` closed and any `Y′ ⊆ Y`.

**What the formalisation finds.** Proposition 7 holds, with the stack hypothesis the reading
adds, and only for covers by two opens. (i) ⟹ (ii) is formal: Corollaire 8 applied to
`cl{x}`, for any space and any fibered category. In (ii) ⟹ (i) the three properties go
separately: pointwise faithfulness gives faithfulness, pointwise fullness gives fullness,
and pointwise essential surjectivity alone gives essential surjectivity — the gluing step of
p. 26 does not use `(P₁)`, `(P₂)`, contrary to « Reste le cas `P₃`, quand `P₁`, `P₂` sont déjà
vérifiés » (they are needed only to conclude an equivalence). What the noetherian induction
uses of `X` is: every non-empty closed set has a point `x` and a neighbourhood `W₀` with
`W₀ ∩ Y ⊆ cl{x}` (`exists_maximal_point`); the case `x ∉ V` is settled by `V ∩ cl{x} = ∅`.
The identification of p. 23 (`𝓕_(x)` on `X_(x)`) is not formalised.

What this certifies is that the reading holds together at these points, not that it is what
the pages say (issue #26).
-/

open CategoryTheory TopologicalSpace Opposite

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

theorem res_refl (V : Opens X) : res F (le_refl V) = 𝟭 _ := by
  simp only [res]
  rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl, F.map_id]
  rfl

theorem obj_res_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : F.obj (op U)) :
    (res F h₂).obj ((res F h₁).obj f) = (res F (h₂.trans h₁)).obj f :=
  Functor.congr_obj (res_comp F h₁ h₂) f

theorem map_res_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) {f g : F.obj (op U)}
    (a : f ⟶ g) : (res F h₂).map ((res F h₁).map a) =
      eqToHom (obj_res_res F h₁ h₂ f) ≫ (res F (h₂.trans h₁)).map a ≫
        eqToHom (obj_res_res F h₁ h₂ g).symm :=
  Functor.congr_hom (res_comp F h₁ h₂) a

variable {F}

/-- Restriction `ρ_{S ≤ T}` on the presheaf `T ↦ Hom(f|T, g|T)` of a pair of objects over `V`. -/
def ρ {V T S : Opens X} {h : T ≤ V} (h₁ : S ≤ T) {f g : F.obj (op V)}
    (a : (res F h).obj f ⟶ (res F h).obj g) :
    (res F (h₁.trans h)).obj f ⟶ (res F (h₁.trans h)).obj g :=
  eqToHom (obj_res_res F h h₁ f).symm ≫ (res F h₁).map a ≫ eqToHom (obj_res_res F h h₁ g)

theorem ρ_res {V T S : Opens X} (h : T ≤ V) (h₁ : S ≤ T) {f g : F.obj (op V)} (u : f ⟶ g) :
    ρ h₁ ((res F h).map u) = (res F (h₁.trans h)).map u := by
  simp [ρ, map_res_res]

theorem ρ_refl {V T : Opens X} {h : T ≤ V} {f g : F.obj (op V)}
    (a : (res F h).obj f ⟶ (res F h).obj g) : ρ (le_refl T) a = a := by
  simp [ρ, Functor.congr_hom (res_refl F T) a]

theorem ρ_ρ {V T S R : Opens X} {h : T ≤ V} (h₁ : S ≤ T) (h₂ : R ≤ S) {f g : F.obj (op V)}
    (a : (res F h).obj f ⟶ (res F h).obj g) : ρ h₂ (ρ h₁ a) = ρ (h₂.trans h₁) a := by
  simp [ρ, map_res_res, eqToHom_map]

/-- Changing the base of a morphism between restrictions from `W` to `V ≥ W`. -/
def tr {V W T : Opens X} (hW : W ≤ V) (h : T ≤ W) {f g : F.obj (op V)} :
    ((res F h).obj ((res F hW).obj f) ⟶ (res F h).obj ((res F hW).obj g)) ≃
      ((res F (h.trans hW)).obj f ⟶ (res F (h.trans hW)).obj g) where
  toFun a := eqToHom (obj_res_res F hW h f).symm ≫ a ≫ eqToHom (obj_res_res F hW h g)
  invFun b := eqToHom (obj_res_res F hW h f) ≫ b ≫ eqToHom (obj_res_res F hW h g).symm
  left_inv a := by simp
  right_inv b := by simp

theorem ρ_eq_tr {V W T : Opens X} (hW : W ≤ V) (h : T ≤ W) {f g : F.obj (op V)}
    (u : (res F hW).obj f ⟶ (res F hW).obj g) : ρ h u = tr hW h ((res F h).map u) := rfl

theorem tr_ρ {V W T S : Opens X} (hW : W ≤ V) (h : T ≤ W) (h₁ : S ≤ T) {f g : F.obj (op V)}
    (a : (res F h).obj ((res F hW).obj f) ⟶ (res F h).obj ((res F hW).obj g)) :
    tr hW (h₁.trans h) (ρ h₁ a) = ρ h₁ (tr hW h a) := by
  simp [tr, ρ, eqToHom_map]

theorem res_res_iff {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) {f g : F.obj (op U)}
    (a b : f ⟶ g) : (res F h₂).map ((res F h₁).map a) = (res F h₂).map ((res F h₁).map b) ↔
      (res F (h₂.trans h₁)).map a = (res F (h₂.trans h₁)).map b := by
  simp [map_res_res, cancel_epi, cancel_mono]


variable (F)

/-! ### The conditions of Définition 6 -/

/-- `(P₁)` relative to `Y`: for every open `V`, restriction `𝓕(V) ⥤ 𝓕(V - Y)` is faithful. -/
def P1 (Y : Set X) : Prop :=
  ∀ ⦃V T : Opens X⦄ (h : T ≤ V), (T : Set X) = (V : Set X) \ Y → (res F h).Faithful

/-- `(P₂)` relative to `Y`: restriction is fully faithful. -/
def P2 (Y : Set X) : Prop :=
  ∀ ⦃V T : Opens X⦄ (h : T ≤ V), (T : Set X) = (V : Set X) \ Y → (res F h).Full ∧ (res F h).Faithful

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

/-! ### Corollaire 8 and (i) ⟹ (ii) -/

variable {F}

/-- The open `V - Y`, for `Y` closed. -/
def diffOpen (V : Opens X) {Y : Set X} (hY : IsClosed Y) : Opens X :=
  ⟨(V : Set X) \ Y, V.isOpen.sdiff hY⟩

theorem diffOpen_le {Y Y' : Set X} (hY : IsClosed Y) (hY' : Y' ⊆ Y) {V T' : Opens X}
    (hT' : (T' : Set X) = (V : Set X) \ Y') : diffOpen V hY ≤ T' := fun y hy => by
  change y ∈ (T' : Set X); rw [hT']; exact ⟨hy.1, fun h => hy.2 (hY' h)⟩

theorem diffOpen_eq {Y Y' : Set X} (hY : IsClosed Y) (hY' : Y' ⊆ Y) {V T' : Opens X}
    (hT' : (T' : Set X) = (V : Set X) \ Y') :
    ((diffOpen V hY : Opens X) : Set X) = (T' : Set X) \ Y := by
  ext y
  simp only [diffOpen, Opens.coe_mk, Set.mem_sdiff, hT']
  exact ⟨fun h => ⟨⟨h.1, fun h' => h.2 (hY' h')⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem corollaire8_P1 {Y Y' : Set X} (hY : IsClosed Y) (hP : P1 F Y) (hY' : Y' ⊆ Y) :
    P1 F Y' := by
  intro V T' h hT'
  have hTT' := diffOpen_le hY hY' hT'
  have := hP (hTT'.trans h) rfl
  rw [← res_comp F h hTT'] at this
  exact Functor.Faithful.of_comp _ (res F hTT')

theorem corollaire8_P2 {Y Y' : Set X} (hY : IsClosed Y) (hP : P2 F Y) (hY' : Y' ⊆ Y) :
    P2 F Y' := by
  intro V T' h hT'
  have hTT' := diffOpen_le hY hY' hT'
  obtain ⟨h1, h2⟩ := hP (hTT'.trans h) rfl
  obtain ⟨-, h4⟩ := hP hTT' (diffOpen_eq hY hY' hT')
  rw [← res_comp F h hTT'] at h1 h2
  exact ⟨Functor.Full.of_comp_faithful _ (res F hTT'), Functor.Faithful.of_comp _ (res F hTT')⟩

theorem corollaire8_P3 {Y Y' : Set X} (hY : IsClosed Y) (hP : P3 F Y) (hY' : Y' ⊆ Y) :
    P3 F Y' := by
  intro V T' h hT'
  have hTT' := diffOpen_le hY hY' hT'
  have h1 := hP (hTT'.trans h) rfl
  have h2 := hP hTT' (diffOpen_eq hY hY' hT')
  rw [← res_comp F h hTT'] at h1
  have : (res F h).Full := Functor.Full.of_comp_faithful _ (res F hTT')
  have : (res F h).Faithful := Functor.Faithful.of_comp _ (res F hTT')
  refine { essSurj := ⟨fun e => ?_⟩ }
  obtain ⟨f, ⟨φ⟩⟩ := Functor.EssSurj.mem_essImage (F := res F h ⋙ res F hTT') ((res F hTT').obj e)
  exact ⟨f, ⟨(res F hTT').preimageIso φ⟩⟩

theorem faithfulAt_of_P1 {Y : Set X} (hY : IsClosed Y) (hP : P1 F Y) {x : X} (hx : x ∈ Y) :
    FaithfulAt F x := by
  intro W T h _ hT f g a b hab
  have := corollaire8_P1 hY hP (closure_minimal (Set.singleton_subset_iff.2 hx) hY) h hT
  exact ⟨W, le_rfl, ‹x ∈ W›, congrArg _ ((res F h).map_injective hab)⟩

theorem fullAt_of_P2 {Y : Set X} (hY : IsClosed Y) (hP : P2 F Y) {x : X} (hx : x ∈ Y) :
    FullAt F x := by
  intro W T h hxW hT f g c
  have := (corollaire8_P2 hY hP (closure_minimal (Set.singleton_subset_iff.2 hx) hY) h hT).1
  refine ⟨W, le_rfl, hxW, (res F le_rfl).map ((res F h).preimage c), T, h, le_rfl, hT, ?_⟩
  rw [ρ_res, ρ_refl]
  exact (res F h).map_preimage c

theorem essSurjAt_of_P3 {Y : Set X} (hY : IsClosed Y) (hP : P3 F Y) {x : X} (hx : x ∈ Y) :
    EssSurjAt F x := by
  intro W T h hxW hT e
  have := corollaire8_P3 hY hP (closure_minimal (Set.singleton_subset_iff.2 hx) hY) h hT
  exact ⟨W, le_rfl, hxW, (res F h).objPreimage e, T, h, le_rfl, hT,
    ⟨(res F h).objObjPreimageIso e ≪≫ eqToIso (Functor.congr_obj (res_refl F T) e).symm⟩⟩

/-! ### Noetherian induction -/

/-- In a noetherian quasi-sober space, a non-empty closed `Y` has a point `x` (a maximal
point of `Y`) with a neighbourhood `W₀` such that `W₀ ∩ Y ⊆ cl{x}`. -/
theorem exists_maximal_point [NoetherianSpace X] [QuasiSober X] {Y : Set X} (hY : IsClosed Y)
    (hne : Y.Nonempty) : ∃ x ∈ Y, ∃ W₀ : Opens X, x ∈ W₀ ∧ (W₀ : Set X) ∩ Y ⊆ closure {x} := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hY
  obtain ⟨y, Z₀, hZ₀, -⟩ := hne
  obtain ⟨Z, hZ⟩ := hSf.exists_maximal ⟨Z₀, hZ₀⟩
  have hZS : Z ∈ S := hZ.prop
  set x := (hSi Z hZS).genericPoint
  have hx : closure ({x} : Set X) = Z := by
    rw [(hSi Z hZS).genericPoint_closure_eq, (hSc Z hZS).closure_eq]
  have hfin : {Z' ∈ S | ¬ Z' ⊆ Z}.Finite := hSf.subset fun _ h => h.1
  refine ⟨x, ⟨Z, hZS, hx ▸ subset_closure rfl⟩,
    ⟨(⋃₀ {Z' ∈ S | ¬ Z' ⊆ Z})ᶜ, (hfin.isClosed_sUnion fun Z' h => hSc Z' h.1).isOpen_compl⟩,
    ?_, ?_⟩
  · rintro ⟨Z', ⟨hZ'S, hZ'⟩, hxZ'⟩
    exact hZ' (hZ.2 hZ'S (hx ▸ closure_minimal (Set.singleton_subset_iff.2 hxZ') (hSc Z' hZ'S)))
  · rintro y ⟨hyW, Z', hZ'S, hyZ'⟩
    rw [hx]
    by_contra hyZ
    exact hyW ⟨Z', ⟨hZ'S, fun h => hyZ (h hyZ')⟩, hyZ'⟩

/-- Noetherian induction on the closed subsets of `Y`, removing a neighbourhood of a maximal
point at each step (pages 19 and 25–26). -/
theorem closed_induction [NoetherianSpace X] [QuasiSober X] (Q : Set X → Prop) {Y : Set X}
    (h₀ : Q ∅)
    (hstep : ∀ Y', IsClosed Y' → Y' ⊆ Y → ∀ x ∈ Y', ∀ W₀ : Opens X, x ∈ W₀ →
      (W₀ : Set X) ∩ Y' ⊆ closure {x} → (∀ W : Opens X, W ≤ W₀ → x ∈ W → Q (Y' \ W)) → Q Y') :
    ∀ Y', IsClosed Y' → Y' ⊆ Y → Q Y' := by
  intro Y' hY'
  lift Y' to Closeds X using hY'
  induction Y' using WellFoundedLT.induction with
  | _ Y' IH =>
    intro hY'Y
    rcases (Y' : Set X).eq_empty_or_nonempty with h | h
    · rw [h]; exact h₀
    obtain ⟨x, hx, W₀, hxW₀, hW₀⟩ := exists_maximal_point Y'.isClosed h
    refine hstep _ Y'.isClosed hY'Y x hx W₀ hxW₀ hW₀ fun W _ hxW => ?_
    exact IH ⟨(Y' : Set X) \ W, Y'.isClosed.sdiff W.isOpen⟩
      (IsConcreteLE.lt_iff_le_and_exists.2 ⟨Set.sdiff_subset, x, hx, fun h => h.2 hxW⟩)
      (Set.sdiff_subset.trans hY'Y)

section geometry

variable {Y' : Set X} {x : X} {W₀ V T : Opens X}

theorem geom_out (hW₀ : (W₀ : Set X) ∩ Y' ⊆ closure {x}) (hxV : x ∉ V)
    (hT : (T : Set X) = (V : Set X) \ Y') : (T : Set X) = (V : Set X) \ (Y' \ W₀) := by
  rw [hT]
  ext y
  simp only [Set.mem_sdiff, SetLike.mem_coe, not_and, not_not]
  refine ⟨fun h => ⟨h.1, fun h' => (h.2 h').elim⟩, fun h => ⟨h.1, fun hy => hxV ?_⟩⟩
  exact (specializes_iff_mem_closure.2 (hW₀ ⟨h.2 hy, hy⟩)).mem_open V.isOpen h.1

theorem geom_in (hY' : IsClosed Y') (hx : x ∈ Y') (hW₀ : (W₀ : Set X) ∩ Y' ⊆ closure {x})
    (hT : (T : Set X) = (V : Set X) \ Y') :
    ((T ⊓ W₀ : Opens X) : Set X) = ((V ⊓ W₀ : Opens X) : Set X) \ closure {x} := by
  have hcl := closure_minimal (Set.singleton_subset_iff.2 hx) hY'
  ext y
  simp only [Opens.coe_inf, hT, Set.mem_inter_iff, Set.mem_sdiff, SetLike.mem_coe]
  exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, fun h' => h.1.2 (hcl h')⟩,
    fun h => ⟨⟨h.1.1, fun h' => h.2 (hW₀ ⟨h.1.2, h'⟩)⟩, h.1.2⟩⟩

theorem geom_sup {W' : Opens X} (hW' : W' ≤ V ⊓ W₀) (hT : (T : Set X) = (V : Set X) \ Y') :
    ((T ⊔ W' : Opens X) : Set X) = (V : Set X) \ (Y' \ W') := by
  have := fun y (hy : y ∈ W') => (hW' hy).1
  ext y
  simp only [Opens.coe_sup, hT, Set.mem_union, Set.mem_sdiff, SetLike.mem_coe, not_and, not_not]
  tauto

theorem geom_inter (hY' : IsClosed Y') (hx : x ∈ Y') (hW₀ : (W₀ : Set X) ∩ Y' ⊆ closure {x})
    {W' S : Opens X} (hW' : W' ≤ V ⊓ W₀) (hT : (T : Set X) = (V : Set X) \ Y')
    (hS : (S : Set X) = (W' : Set X) \ closure {x}) : (S : Set X) = (T : Set X) ∩ W' := by
  have hcl := closure_minimal (Set.singleton_subset_iff.2 hx) hY'
  ext y
  simp only [hS, hT, Set.mem_inter_iff, Set.mem_sdiff, SetLike.mem_coe]
  exact ⟨fun h => ⟨⟨(hW' h.1).1, fun h' => h.2 (hW₀ ⟨(hW' h.1).2, h'⟩)⟩, h.1⟩,
    fun h => ⟨h.2, fun h' => h.1.2 (hcl h')⟩⟩

end geometry

/-! ### (ii) ⟹ (i), one property at a time -/

theorem res_of_empty {V T : Opens X} (hT : (T : Set X) = (V : Set X) \ ∅) :
    T = V := Opens.ext (by rw [hT, Set.sdiff_empty])

variable [NoetherianSpace X] [QuasiSober X]

/-- Pointwise faithfulness at the points of `Y` gives `(P₁)` relative to `Y`. -/
theorem P1_of_faithfulAt (hF : IsBinaryPrestack F) {Y : Set X} (hY : IsClosed Y)
    (hx : ∀ x ∈ Y, FaithfulAt F x) : P1 F Y := by
  refine closed_induction (P1 F) ?_ ?_ Y hY subset_rfl
  · intro V T h hT
    obtain rfl := res_of_empty hT
    rw [res_refl]; infer_instance
  intro Y' hY'c hY'Y x hxY' W₀ hxW₀ hW₀ IH V T h hT
  refine ⟨fun {f g} a b hab => ?_⟩
  by_cases hxV : x ∈ V
  · have hTx := geom_in hY'c hxY' hW₀ hT
    have hTxW : T ⊓ W₀ ≤ V ⊓ W₀ := inf_le_inf_right _ h
    have hab' : (res F hTxW).map ((res F (inf_le_left : V ⊓ W₀ ≤ V)).map a) =
        (res F hTxW).map ((res F (inf_le_left : V ⊓ W₀ ≤ V)).map b) := by
      have := congrArg (res F (inf_le_left : T ⊓ W₀ ≤ T)).map hab
      rwa [res_res_iff, ← res_res_iff (h₂ := hTxW)] at this
    obtain ⟨W', h', hxW', hW'⟩ := hx x (hY'Y hxY') hTxW ⟨hxV, hxW₀⟩ hTx _ _ hab'
    rw [res_res_iff] at hW'
    have hT'V : T ⊔ W' ≤ V := sup_le h (h'.trans inf_le_left)
    have := IH W' (h'.trans inf_le_right) hxW' hT'V (geom_sup h' hT)
    apply (res F hT'V).map_injective
    exact hF.ext le_sup_left le_sup_right (Opens.coe_sup _ _) _ _ (by rwa [res_res_iff])
      (by rwa [res_res_iff])
  · have := IH W₀ le_rfl hxW₀ h (geom_out hW₀ hxV hT)
    exact (res F h).map_injective hab

/-- Pointwise fullness at the points of `Y` gives fullness of the restrictions to `V - Y`. -/
theorem full_of_fullAt (hF : IsBinaryPrestack F) {Y : Set X} (hY : IsClosed Y)
    (hx : ∀ x ∈ Y, FullAt F x) :
    ∀ ⦃V T : Opens X⦄ (h : T ≤ V), (T : Set X) = (V : Set X) \ Y → (res F h).Full := by
  refine closed_induction (fun Y => ∀ ⦃V T : Opens X⦄ (h : T ≤ V),
    (T : Set X) = (V : Set X) \ Y → (res F h).Full) ?_ ?_ Y hY subset_rfl
  · intro V T h hT
    obtain rfl := res_of_empty hT
    rw [res_refl]; infer_instance
  intro Y' hY'c hY'Y x hxY' W₀ hxW₀ hW₀ IH V T h hT
  refine ⟨fun {f g} c => ?_⟩
  by_cases hxV : x ∈ V
  · have hTx := geom_in hY'c hxY' hW₀ hT
    have hW : V ⊓ W₀ ≤ V := inf_le_left
    have hTxT : T ⊓ W₀ ≤ T := inf_le_left
    have hTxW : T ⊓ W₀ ≤ V ⊓ W₀ := inf_le_inf_right _ h
    obtain ⟨W', h', hxW', a, S, h₁, h₂, hS, hρ⟩ :=
      hx x (hY'Y hxY') hTxW ⟨hxV, hxW₀⟩ hTx ((tr hW hTxW).symm (ρ hTxT c))
    have hρ' : ρ h₁ (tr hW h' a) = ρ (h₂.trans hTxT) c := by
      have := congrArg (tr hW (h₁.trans h')) hρ
      rwa [tr_ρ, tr_ρ, Equiv.apply_symm_apply, ρ_ρ] at this
    have hT'V : T ⊔ W' ≤ V := sup_le h (h'.trans hW)
    obtain ⟨u, hu₁, hu₂⟩ := hF.glue (le_sup_left : T ≤ T ⊔ W') le_sup_right (h₂.trans hTxT) h₁
      (Opens.coe_sup _ _) (geom_inter hY'c hxY' hW₀ h' hT hS)
      ((tr hT'V le_sup_left).symm c) ((tr hT'V le_sup_right).symm (tr hW h' a)) (by
        apply (tr hT'V ((h₂.trans hTxT).trans le_sup_left)).injective
        rw [tr_ρ, tr_ρ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hρ'.symm)
    have := IH W' (h'.trans inf_le_right) hxW' hT'V (geom_sup h' hT)
    obtain ⟨w, hw⟩ := (res F hT'V).map_surjective u
    refine ⟨w, ?_⟩
    rw [← ρ_res hT'V le_sup_left, hw, ρ_eq_tr, hu₁, Equiv.apply_symm_apply]
  · have := IH W₀ le_rfl hxW₀ h (geom_out hW₀ hxV hT)
    exact (res F h).map_surjective c

/-- Pointwise essential surjectivity at the points of `Y` gives essential surjectivity of the
restrictions to `V - Y`; this is the step of pages 25–26, gluing over `W ∪ U`. -/
theorem essSurj_of_essSurjAt (hF : IsBinaryStack F) {Y : Set X} (hY : IsClosed Y)
    (hx : ∀ x ∈ Y, EssSurjAt F x) :
    ∀ ⦃V T : Opens X⦄ (h : T ≤ V), (T : Set X) = (V : Set X) \ Y → (res F h).EssSurj := by
  refine closed_induction (fun Y => ∀ ⦃V T : Opens X⦄ (h : T ≤ V),
    (T : Set X) = (V : Set X) \ Y → (res F h).EssSurj) ?_ ?_ Y hY subset_rfl
  · intro V T h hT
    obtain rfl := res_of_empty hT
    rw [res_refl]; infer_instance
  intro Y' hY'c hY'Y x hxY' W₀ hxW₀ hW₀ IH V T h hT
  refine ⟨fun e => ?_⟩
  by_cases hxV : x ∈ V
  · have hTx := geom_in hY'c hxY' hW₀ hT
    have hTxT : T ⊓ W₀ ≤ T := inf_le_left
    have hTxW : T ⊓ W₀ ≤ V ⊓ W₀ := inf_le_inf_right _ h
    obtain ⟨W', h', hxW', f₀, S, h₁, h₂, hS, ⟨φ⟩⟩ :=
      hx x (hY'Y hxY') hTxW ⟨hxV, hxW₀⟩ hTx ((res F hTxT).obj e)
    obtain ⟨t, ⟨φt⟩, -⟩ := hF.glueObj (le_sup_left : T ≤ T ⊔ W') le_sup_right (h₂.trans hTxT) h₁
      (Opens.coe_sup _ _) (geom_inter hY'c hxY' hW₀ h' hT hS) e f₀
      ⟨eqToIso (obj_res_res F hTxT h₂ e).symm ≪≫ φ.symm⟩
    have hT'V : T ⊔ W' ≤ V := sup_le h (h'.trans inf_le_left)
    have := IH W' (h'.trans inf_le_right) hxW' hT'V (geom_sup h' hT)
    obtain ⟨F₀, ⟨χ⟩⟩ := Functor.EssSurj.mem_essImage (F := res F hT'V) t
    exact ⟨F₀, ⟨eqToIso (obj_res_res F hT'V le_sup_left F₀).symm ≪≫
      (res F le_sup_left).mapIso χ ≪≫ φt⟩⟩
  · have := IH W₀ le_rfl hxW₀ h (geom_out hW₀ hxV hT)
    exact Functor.EssSurj.mem_essImage (F := res F h) e

/-! ### Proposition 7 -/

/-- **Proposition 7, `(P₁)`.** For a binary prestack over a noetherian quasi-sober space
(e.g. noetherian spectral) and `Y` closed, `(P₁)` relative to `Y` holds iff it holds at every
point of `Y`. -/
theorem proposition7_P1 (hF : IsBinaryPrestack F) {Y : Set X} (hY : IsClosed Y) :
    P1 F Y ↔ ∀ x ∈ Y, FaithfulAt F x :=
  ⟨fun hP _ hx => faithfulAt_of_P1 hY hP hx, P1_of_faithfulAt hF hY⟩

/-- **Proposition 7, `(P₂)`.** -/
theorem proposition7_P2 (hF : IsBinaryPrestack F) {Y : Set X} (hY : IsClosed Y) :
    P2 F Y ↔ ∀ x ∈ Y, FullAt F x ∧ FaithfulAt F x :=
  ⟨fun hP _ hx => ⟨fullAt_of_P2 hY hP hx, faithfulAt_of_P1 hY (fun _ _ h hT => (hP h hT).2) hx⟩,
    fun H _ _ h hT => ⟨full_of_fullAt hF hY (fun x hx => (H x hx).1) h hT,
      P1_of_faithfulAt hF hY (fun x hx => (H x hx).2) h hT⟩⟩

/-- **Proposition 7, `(P₃)`**, for a stack (binary covers suffice): restriction to `V - Y` is
an equivalence for every open `V` iff the induced functor on germs at each `x ∈ Y` is one. -/
theorem proposition7_P3 (hF : IsBinaryStack F) {Y : Set X} (hY : IsClosed Y) :
    P3 F Y ↔ ∀ x ∈ Y, (FullAt F x ∧ FaithfulAt F x) ∧ EssSurjAt F x := by
  refine ⟨fun hP x hx => ⟨(proposition7_P2 hF.toIsBinaryPrestack hY).1
    (fun _ _ h hT => ⟨(hP h hT).full, (hP h hT).faithful⟩) x hx, essSurjAt_of_P3 hY hP hx⟩,
    fun H V T h hT => ?_⟩
  obtain ⟨h₁, h₂⟩ := (proposition7_P2 hF.toIsBinaryPrestack hY).2 (fun x hx => (H x hx).1) h hT
  exact { essSurj := essSurj_of_essSurjAt hF hY (fun x hx => (H x hx).2) h hT }

end Grothendieck.Folder21.Stack
