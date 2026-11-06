module

public import Mathlib

@[expose] public section


/-!
# Folder 120, pages 20–23: collapsing a tame subset over a field

The modernised reading `transcripts/120/120.modern.tex` (« Topologie modérée », dated by the
inventory « à partir de 1973 — à partir de 1978 ») sets up, for a set `R`, families
`𝓜_I ⊂ 𝔓(R^I)` of *tame* subsets indexed by the finite sets `I`, subject to (M′1)–(M′4):
stability by `u^* : R^J → R^I`, `x ↦ x ∘ u` (direct images, preimages for `u` surjective,
cuts `A ∩ (u^*)⁻¹ B`), and products. A map is tame when its graph is a tame subset; a *tame
function* on `X ∈ 𝓜_I` is a map `X → R` whose graph lies in `𝓜_{I ⊔ 1}`; the tame points
`R₀` are the `c` with `{c} ∈ 𝓜_1`. Axiom (M6) asks that a tame `Y ⊂ X` be a fibre
`⋂ f_α⁻¹(e_α)`, `e_α ∈ R₀`, of finitely many tame functions, « and one may assume that the
`f_α` separate the points of `X ∖ Y` », which says that `X/Y` exists in the strict sense.
Section (VI) supposes `R` a field with (M11): `0, 1` tame points, `x - y` and `xy` tame on
every `A ∈ 𝓜₂`, tame sets of inverses. It states:

> **Proposition (page 23).** Under (M1)–(M7) and (M11), every tame subset `Y` of a tame space
> `X` which is the common zero set of finitely many tame functions is also that of a finite
> family of tame functions separating the points of `X ∖ Y`; that is, `X/Y` is a tame space.

The proof (pages 22–23): translate to `e_α = 0`, take tame `g_β` embedding `X`, and use the
`f_α` and the `f_α g_β`; for `x ≠ y` off `Y` not separated by the `f_α`, some
`λ = f_α(x) ≠ 0` and some `g_β(x) ≠ g_β(y)` give `λ g_β(x) ≠ λ g_β(y)`.
This is finding `120-collapse-separation-over-a-field` of `src/content/findings.ts`.

What is formalised. The axioms are those of the reading in the form (M′1)–(M′4) it uses
(`TameModel`, index types finite), (M11) b) as `RingOps`, (M11) in full as `M11` for a field.

* `TameModel.isTameFun_mul`, `isTameFun_sub`, `isTameFun_const`, `isTameFun_coord`: the tame
  functions on a tame `X` are stable by `-` and `·`, contain the constants of `R₀` and the
  coordinates. Only (M′1), (M′2), (M′4) and (M11) b) are used.
* `separates_off_zeroSet` (any commutative ring without zero divisors, any set `X`, no
  finiteness): the family `f_α`, `f_α g_β` has the zero set of the `f_α` and separates the
  points off it as soon as the `g_β` separate points. `not_separates_zmod4`: with zero
  divisors it fails (`ℤ/4`, `f = 2`, `g = id`).
* `collapse_separation` (page 23 with the translation of page 22): for `X ∈ 𝓜_I`, tame `f_α`,
  `e_α ∈ R₀`, tame `g_β` injective on `X`, the functions `f_α - e_α` and `(f_α - e_α) g_β`
  are tame, vanish together exactly on `Y = ⋂ f_α⁻¹(e_α)`, and separate the points of
  `X ∖ Y`. `exists_separating_family` and `exists_separating_family_of_field` state the
  Proposition as an existence, the second under (M11) for a field.

The statement holds, more generally: neither (M3), (M5)–(M7), (M11) a), c), nor the
finiteness of the families is used, and « field » can be weakened to « no zero divisors ».
The reading's corrections `e_α ∈ R₀` (page 22) and `X ∖ Y` (page 23) are both needed: the
first for the translation, the second because a family constant on `Y` cannot separate two
points of `Y`.
## Pushouts along tame embeddings (pages 8 to 13), finding `120-axiomatic-pushouts-along-embeddings`

Axioms (M5′) `Unions` (∅ and binary unions), (M6) `M6` (a tame `Z ⊂ X` is a fibre `F⁻¹(e)`,
`e ∈ R₀^A`, of a tame family injective off `Z`), (M7) `M7` (tame functions extend from tame
subsets). Spaces are tame subsets `X ⊂ R^I`, maps are families with tame graph.

* `graph_mem_of_coords`, `isTameFun_of_graph`: a finite family has a tame graph iff its
  coordinates are tame functions ((M′1), (M′2), (M′4), induction on the index set).
* `pushout_of_criterion` (pp. 10–11, sufficiency, with the principle of pp. 8 and 11):
  compatible tame families `J₁`, `J₂` that are injective and separate the two sides off `Z`
  give a tame `J₁(X₁) ∪ J₂(X₂)`, which is the set-theoretic pushout and has the universal
  property for tame maps.
* `side_data`, `pushout_exists` (pp. 12–13): under (M5′), (M6), (M7), two tame embeddings
  `Z ↪ X₁`, `Z ↪ X₂` have such a pushout, by diagram (*): `X₁` on the level `e₂`, `X₂` on the
  level `e₁` of `R^K × R^{A₁} × R^{A₂}`, the `R^K` coordinate extending `Z ⊂ R^K` by (M7).

What the formalisation found: the Proposition holds, with the reading's restored
conclusion (the two images meet exactly along `Z`). It needs `R` non-empty for the universal
property, as a map into `R^L` must exist (the trivial cases of page 4 excluded); (M5′) is
used only for the union `J₁(X₁) ∪ J₂(X₂)` and for the graph of the induced map; (M6) needs its
« de plus » half (injectivity off `Z`), which the reading notes does not follow from the first
over a general `R`. The category `Σ` of abstract tame spaces and the NB for finite diagrams
are not formalised.
-/

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

/-- The joint graph of two tame functions is tame ((M′2) and (M′4)). -/
theorem graphOn_pair_mem {I : Type} [Finite I] {X : Set (I → R)} {f g : (I → R) → R}
    (hf : T.IsTameFun X f) (hg : T.IsTameFun X g) :
    graphOn X (fun x => ![f x, g x]) ∈ T.M (I ⊕ Fin 2) := by
  let w : (I ⊕ Unit) ⊕ (I ⊕ Unit) → I ⊕ Fin 2 := fun
    | .inl (.inl i) => .inl i
    | .inl (.inr _) => .inr 0
    | .inr (.inl i) => .inl i
    | .inr (.inr _) => .inr 1
  have hw : Surjective w := by
    rintro (i | k)
    · exact ⟨.inl (.inl i), rfl⟩
    · fin_cases k
      exacts [⟨.inl (.inr ()), rfl⟩, ⟨.inr (.inr ()), rfl⟩]
  convert T.m2 w hw (T.m4 hf hg) using 1
  ext y
  constructor
  · rintro ⟨hX, hk⟩
    exact ⟨⟨hX, fun _ => hk 0⟩, hX, fun _ => hk 1⟩
  · rintro ⟨⟨hX, h0⟩, -, h1⟩
    refine ⟨hX, fun k => ?_⟩
    fin_cases k
    exacts [h0 (), h1 ()]

/-- The image `F(X)` of `X` by a family with tame graph is tame ((M′1)). -/
theorem image_mem {I K : Type} [Finite I] [Finite K] {X : Set (I → R)}
    {F : (I → R) → K → R} (hF : graphOn X F ∈ T.M (I ⊕ K)) : F '' X ∈ T.M K := by
  convert T.m1 Sum.inr hF using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Sum.elim x (F x), ⟨hx, fun _ => rfl⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hk⟩, rfl⟩
    exact ⟨y ∘ Sum.inl, hy, funext fun k => (hk k).symm⟩

/-- Composition: a tame function of a family with tame graph is tame ((M′1), (M′2),
(M′4)). -/
theorem isTameFun_comp {I K : Type} [Finite I] [Finite K] {X : Set (I → R)}
    {F : (I → R) → K → R} (hF : graphOn X F ∈ T.M (I ⊕ K)) {h : (K → R) → R}
    (hh : T.IsTameFun (F '' X) h) : T.IsTameFun X (fun x => h (F x)) := by
  let w : (I ⊕ K) ⊕ (K ⊕ Unit) → (I ⊕ K) ⊕ Unit := fun
    | .inl p => .inl p
    | .inr (.inl k) => .inl (.inr k)
    | .inr (.inr _) => .inr ()
  have hw : Surjective w := by
    rintro (p | _)
    · exact ⟨.inl p, rfl⟩
    · exact ⟨.inr (.inr ()), rfl⟩
  let v : I ⊕ Unit → (I ⊕ K) ⊕ Unit := fun
    | .inl i => .inl (.inl i)
    | .inr _ => .inr ()
  unfold IsTameFun
  convert T.m1 v (T.m2 w hw (T.m4 hF hh)) using 1
  ext z
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨hz, hk⟩
    refine ⟨Sum.elim (Sum.elim (z ∘ Sum.inl) (F (z ∘ Sum.inl))) (fun _ => z (.inr ())),
      ⟨⟨hz, fun _ => rfl⟩, ⟨_, hz, rfl⟩, fun _ => hk ()⟩, ?_⟩
    funext i
    rcases i with i | _ <;> rfl
  · rintro ⟨y, ⟨⟨hy, hyk⟩, -, hyh⟩, rfl⟩
    exact ⟨hy, fun _ => (hyh ()).trans (congrArg h (funext hyk))⟩

/-- The tame functions are stable by product (page 20). -/
theorem isTameFun_mul [CommRing R] (h11 : T.RingOps) {I : Type} [Finite I]
    {X : Set (I → R)} {f g : (I → R) → R} (hf : T.IsTameFun X f) (hg : T.IsTameFun X g) :
    T.IsTameFun X (fun x => f x * g x) := by
  have hP := T.graphOn_pair_mem hf hg
  simpa using T.isTameFun_comp hP (h11 _ (T.image_mem hP)).2

/-- The tame functions are stable by difference (page 20). -/
theorem isTameFun_sub [CommRing R] (h11 : T.RingOps) {I : Type} [Finite I]
    {X : Set (I → R)} {f g : (I → R) → R} (hf : T.IsTameFun X f) (hg : T.IsTameFun X g) :
    T.IsTameFun X (fun x => f x - g x) := by
  have hP := T.graphOn_pair_mem hf hg
  simpa using T.isTameFun_comp hP (h11 _ (T.image_mem hP)).1

/-- A constant `c ∈ R₀` is a tame function on a tame `X` ((M′4)): its graph is `X × {c}`. -/
theorem isTameFun_const {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) {c : R}
    (hc : c ∈ T.R0) : T.IsTameFun X (fun _ => c) := by
  unfold IsTameFun
  convert T.m4 hX hc using 1
  ext y
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact and_congr_right fun _ => ⟨fun h => funext h, fun h k => congrFun h k⟩

/-- The coordinates are tame functions on a tame `X` ((M′1)). -/
theorem isTameFun_coord {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) (i : I) :
    T.IsTameFun X (fun x => x i) := by
  unfold IsTameFun
  convert T.m1 (Sum.elim id fun _ => i : I ⊕ Unit → I) hX using 1
  ext y
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hy, hk⟩
    refine ⟨y ∘ Sum.inl, hy, funext fun j => ?_⟩
    rcases j with j | _
    · rfl
    · exact (hk ()).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, fun _ => rfl⟩

end TameModel

/-- The family of page 22: the `f_α` and the products `f_α g_β`. -/
def collapseFamily {R X A B : Type*} [Mul R] (f : A → X → R) (g : B → X → R) :
    A ⊕ A × B → X → R :=
  Sum.elim f fun p x => f p.1 x * g p.2 x

/-- The family has the common zero set of the `f_α`. -/
theorem collapseFamily_eq_zero_iff {R X A B : Type*} [MulZeroClass R] (f : A → X → R)
    (g : B → X → R) (x : X) : (∀ c, collapseFamily f g c x = 0) ↔ ∀ a, f a x = 0 := by
  refine ⟨fun h a => h (.inl a), fun h c => ?_⟩
  rcases c with a | ⟨a, b⟩
  · exact h a
  · simp [collapseFamily, h a]

/-- Pages 22–23, the argument: if `x` is off the zero set of the `f_α` and some `g_β`
separates `x` and `y`, the `f_α` and `f_α g_β` separate `x` and `y`. Any ring without zero
divisors, any set. -/
theorem separates_off_zeroSet {R X A B : Type*} [Ring R] [NoZeroDivisors R] (f : A → X → R)
    (g : B → X → R) {x y : X} (hx : ∃ a, f a x ≠ 0) (hg : ∃ b, g b x ≠ g b y) :
    ∃ c, collapseFamily f g c x ≠ collapseFamily f g c y := by
  by_contra! h
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hg
  have h1 : f a x = f a y := h (.inl a)
  have h2 : f a x * g b x = f a y * g b y := h (.inr (a, b))
  rw [← h1] at h2
  exact hb (mul_left_cancel₀ ha h2)

/-- Zero divisors break the argument: over `ℤ/4`, `f = 2` and `g = id`, the family `2, 2x`
does not separate `0` and `2`, though `f(0) ≠ 0` and `g(0) ≠ g(2)`. -/
theorem not_separates_zmod4 :
    ¬ ∃ c, collapseFamily (fun (_ : Unit) (_ : ZMod 4) => (2 : ZMod 4))
      (fun (_ : Unit) (x : ZMod 4) => x) c 0 ≠
      collapseFamily (fun (_ : Unit) (_ : ZMod 4) => (2 : ZMod 4))
      (fun (_ : Unit) (x : ZMod 4) => x) c 2 := by
  decide

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-- **Proposition (page 23)**, with the translation of page 22: for tame `f_α`, tame points
`e_α`, and tame `g_β` embedding `X`, the functions `f_α - e_α` and `(f_α - e_α) g_β` are tame,
vanish together exactly on `Y = ⋂ f_α⁻¹(e_α)`, and separate the points of `X ∖ Y`. -/
theorem collapse_separation [CommRing R] [NoZeroDivisors R] (h11 : T.RingOps) {I : Type}
    [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) {A B : Type} (f : A → (I → R) → R)
    (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R) (he : ∀ a, e a ∈ T.R0)
    (g : B → (I → R) → R) (hg : ∀ b, T.IsTameFun X (g b))
    (hinj : Set.InjOn (fun x b => g b x) X) :
    (∀ c, T.IsTameFun X (collapseFamily (fun a x => f a x - e a) g c)) ∧
    (∀ x, (∀ c, collapseFamily (fun a x => f a x - e a) g c x = 0) ↔ ∀ a, f a x = e a) ∧
    ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y →
      ∃ c, collapseFamily (fun a x => f a x - e a) g c x ≠
        collapseFamily (fun a x => f a x - e a) g c y := by
  have hf' : ∀ a, T.IsTameFun X (fun x => f a x - e a) := fun a =>
    T.isTameFun_sub h11 (hf a) (T.isTameFun_const hX (he a))
  refine ⟨?_, fun x => ?_, fun x hx y hy hxy hne => ?_⟩
  · rintro (a | ⟨a, b⟩)
    · exact hf' a
    · exact T.isTameFun_mul h11 (hf' a) (hg b)
  · exact (collapseFamily_eq_zero_iff _ _ x).trans (forall_congr' fun a => sub_eq_zero)
  · exact separates_off_zeroSet _ g (hxy.imp fun a => sub_ne_zero.mpr)
      (not_forall.mp fun h => hne (hinj hx hy (funext h)))

/-- **Proposition (page 23)** as an existence: a tame `Y = ⋂ f_α⁻¹(e_α)` of a tame `X` is the
common zero set of a finite family of tame functions separating the points of `X ∖ Y`
(the coordinates serve as the `g_β`). -/
theorem exists_separating_family [CommRing R] [NoZeroDivisors R] (h11 : T.RingOps)
    {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I) {A : Type} [Finite A]
    (f : A → (I → R) → R) (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R)
    (he : ∀ a, e a ∈ T.R0) :
    ∃ (C : Type) (_ : Finite C) (h : C → (I → R) → R), (∀ c, T.IsTameFun X (h c)) ∧
      (∀ x, (∀ c, h c x = 0) ↔ ∀ a, f a x = e a) ∧
      ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y → ∃ c, h c x ≠ h c y :=
  ⟨A ⊕ A × I, inferInstance, _, T.collapse_separation h11 hX f hf e he (fun i x => x i)
    (T.isTameFun_coord hX) fun _ _ _ _ h => h⟩

/-- The Proposition under (M11) for a field, as the page states it. -/
theorem exists_separating_family_of_field [Field R] (h11 : T.M11) {I : Type} [Finite I]
    {X : Set (I → R)} (hX : X ∈ T.M I) {A : Type} [Finite A] (f : A → (I → R) → R)
    (hf : ∀ a, T.IsTameFun X (f a)) (e : A → R) (he : ∀ a, e a ∈ T.R0) :
    ∃ (C : Type) (_ : Finite C) (h : C → (I → R) → R), (∀ c, T.IsTameFun X (h c)) ∧
      (∀ x, (∀ c, h c x = 0) ↔ ∀ a, f a x = e a) ∧
      ∀ x ∈ X, ∀ y ∈ X, (∃ a, f a x ≠ e a) → x ≠ y → ∃ c, h c x ≠ h c y :=
  T.exists_separating_family h11.ringOps hX f hf e he

end TameModel

/-- Page 23's « sépare les points de X » cannot be meant literally: a family vanishing on
`Y` does not separate two distinct points of `Y`. -/
theorem not_separates_on_zeroSet {R X C : Type*} [Zero R] (h : C → X → R) {x y : X}
    (hx : ∀ c, h c x = 0) (hy : ∀ c, h c y = 0) : ∀ c, h c x = h c y := fun c => by
  rw [hx, hy]

namespace TameModel

variable {R : Type u} (T : TameModel R)

/-! ## Pushouts along tame embeddings (pages 8 to 13), finding
`120-axiomatic-pushouts-along-embeddings` -/

/-- (M5′) (page 9): each `𝓜_I` contains `∅` and is stable under binary unions. -/
def Unions : Prop :=
  ∀ (I : Type) [Finite I], ∅ ∈ T.M I ∧ ∀ A ∈ T.M I, ∀ B ∈ T.M I, A ∪ B ∈ T.M I

/-- (M6) (page 12): a tame `Z ⊂ X` is the fibre `F⁻¹(e)` over a tame point of a finite tame
family `F : X → R^A`, which may be taken injective off `Z`. -/
def M6 : Prop :=
  ∀ {I : Type} [Finite I] {X Z : Set (I → R)}, X ∈ T.M I → Z ∈ T.M I → Z ⊆ X →
    ∃ (A : Type) (_ : Finite A) (F : (I → R) → A → R) (e : A → R),
      graphOn X F ∈ T.M (I ⊕ A) ∧ (∀ a, e a ∈ T.R0) ∧ (∀ x ∈ X, x ∈ Z ↔ F x = e) ∧
        Set.InjOn F (X \ Z)

/-- (M7) (page 12), a tame Tietze theorem: a tame function on a tame `Z ⊂ X` extends to a
tame function on `X`. -/
def M7 : Prop :=
  ∀ {I : Type} [Finite I] {X Z : Set (I → R)} {f : (I → R) → R}, X ∈ T.M I → Z ∈ T.M I →
    Z ⊆ X → T.IsTameFun Z f → ∃ g : (I → R) → R, T.IsTameFun X g ∧ ∀ z ∈ Z, g z = f z

/-- The coordinates of a family with tame graph are tame functions ((M′1)). -/
theorem isTameFun_of_graph {I K : Type} [Finite I] [Finite K] {X : Set (I → R)}
    {F : (I → R) → K → R} (hF : graphOn X F ∈ T.M (I ⊕ K)) (k : K) :
    T.IsTameFun X (fun x => F x k) := by
  unfold IsTameFun
  convert T.m1 (Sum.elim Sum.inl fun _ => Sum.inr k : I ⊕ Unit → I ⊕ K) hF using 1
  ext y
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hy, hk⟩
    refine ⟨Sum.elim (y ∘ Sum.inl) (F (y ∘ Sum.inl)), ⟨hy, fun _ => rfl⟩, funext fun j => ?_⟩
    rcases j with j | _
    · rfl
    · exact (hk ()).symm
  · rintro ⟨z, ⟨hz, hk⟩, rfl⟩
    exact ⟨hz, fun _ => hk k⟩

/-- A finite family of tame functions on a tame `X` has a tame graph ((M′1), (M′2), (M′4),
by induction on the index set). -/
theorem graph_mem_of_coords {I : Type} [Finite I] {X : Set (I → R)} (hX : X ∈ T.M I)
    {K : Type} [Finite K] {F : (I → R) → K → R} (hF : ∀ k, T.IsTameFun X (fun x => F x k)) :
    graphOn X F ∈ T.M (I ⊕ K) := by
  suffices h : ∀ K : Type, Finite K → ∀ F : (I → R) → K → R,
      (∀ k, T.IsTameFun X (fun x => F x k)) → graphOn X F ∈ T.M (I ⊕ K) from
    h K inferInstance F hF
  intro K hK
  refine Finite.induction_empty_option (P := fun K : Type => Finite K →
    ∀ F : (I → R) → K → R, (∀ k, T.IsTameFun X (fun x => F x k)) → graphOn X F ∈ T.M (I ⊕ K))
    ?_ ?_ ?_ K hK
  · intro α β e ih hβ F hF
    have : Finite α := Finite.of_equiv _ e.symm
    have hα := ih this (fun x a => F x (e a)) (fun a => hF (e a))
    convert T.m1 (Sum.map id e.symm : I ⊕ β → I ⊕ α) hα using 1
    ext y
    simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hy, hk⟩
      refine ⟨Sum.elim (y ∘ Sum.inl) (fun a => F (y ∘ Sum.inl) (e a)),
        ⟨hy, fun _ => rfl⟩, funext fun j => ?_⟩
      rcases j with j | b
      · rfl
      · simp [hk b]
    · rintro ⟨z, ⟨hz, hk⟩, rfl⟩
      refine ⟨hz, fun b => ?_⟩
      have := hk (e.symm b)
      rw [Equiv.apply_symm_apply] at this
      exact this
  · intro _ F _
    convert T.m1 (Sum.elim id PEmpty.elim : I ⊕ PEmpty → I) hX using 1
    ext y
    simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hy, -⟩
      refine ⟨y ∘ Sum.inl, hy, funext fun j => ?_⟩
      cases j with
      | inl j => rfl
      | inr j => exact j.elim
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, fun k => k.elim⟩
  · intro α _ ih _ F hF
    have hα := ih inferInstance (fun x a => F x (some a)) (fun a => hF (some a))
    have hn := hF none
    let w : (I ⊕ α) ⊕ (I ⊕ Unit) → I ⊕ Option α := fun
      | .inl (.inl i) => .inl i
      | .inl (.inr a) => .inr (some a)
      | .inr (.inl i) => .inl i
      | .inr (.inr _) => .inr none
    have hw : Surjective w := by
      rintro (i | (_ | a))
      · exact ⟨.inl (.inl i), rfl⟩
      · exact ⟨.inr (.inr ()), rfl⟩
      · exact ⟨.inl (.inr a), rfl⟩
    convert T.m2 w hw (T.m4 hα hn) using 1
    ext y
    simp only [graphOn, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hy, hk⟩
      exact ⟨⟨hy, fun a => hk (some a)⟩, hy, fun _ => hk none⟩
    · rintro ⟨⟨hy, hk⟩, -, hn'⟩
      refine ⟨hy, fun o => ?_⟩
      rcases o with _ | a
      · exact hn' ()
      · exact hk a

/-- **The criterion of pages 10 and 11** (sufficiency, under (M5′)). Let `J₁`, `J₂` be tame
families on `X₁`, `X₂` with values in `R^N` such that a) `J₁ i₁ = J₂ i₂` on `Z`, b) `J₁`,
`J₂` are injective, c) `J₁ x₁ ≠ J₂ x₂` off `i₁(Z)`, `i₂(Z)`. Then `P = J₁(X₁) ∪ J₂(X₂)` is
tame, it is the set-theoretic pushout (`J₁ x₁ = J₂ x₂` iff `x₁ = i₁ z`, `x₂ = i₂ z`), and it
has the universal property for tame maps (the principle of pages 8 and 11). -/
theorem pushout_of_criterion [Nonempty R] (hU : T.Unions) {I₁ I₂ K N : Type} [Finite I₁] [Finite I₂]
    [Finite N] {X₁ : Set (I₁ → R)} {X₂ : Set (I₂ → R)} {Z : Set (K → R)}
    (hX₁ : X₁ ∈ T.M I₁) (hX₂ : X₂ ∈ T.M I₂) {i₁ : (K → R) → I₁ → R} {i₂ : (K → R) → I₂ → R}
    (hi₁ : Set.MapsTo i₁ Z X₁) (hi₂ : Set.MapsTo i₂ Z X₂)
    {J₁ : (I₁ → R) → N → R} {J₂ : (I₂ → R) → N → R}
    (hJ₁ : graphOn X₁ J₁ ∈ T.M (I₁ ⊕ N)) (hJ₂ : graphOn X₂ J₂ ∈ T.M (I₂ ⊕ N))
    (ha : ∀ z ∈ Z, J₁ (i₁ z) = J₂ (i₂ z)) (hb₁ : Set.InjOn J₁ X₁) (hb₂ : Set.InjOn J₂ X₂)
    (hc : ∀ x₁ ∈ X₁, (∀ z ∈ Z, x₁ ≠ i₁ z) → ∀ x₂ ∈ X₂, (∀ z ∈ Z, x₂ ≠ i₂ z) →
      J₁ x₁ ≠ J₂ x₂) :
    J₁ '' X₁ ∪ J₂ '' X₂ ∈ T.M N ∧
    (∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂, J₁ x₁ = J₂ x₂ ↔ ∃ z ∈ Z, x₁ = i₁ z ∧ x₂ = i₂ z) ∧
    ∀ (L : Type) [Finite L] (f₁ : (I₁ → R) → L → R) (f₂ : (I₂ → R) → L → R),
      graphOn X₁ f₁ ∈ T.M (I₁ ⊕ L) → graphOn X₂ f₂ ∈ T.M (I₂ ⊕ L) →
      (∀ z ∈ Z, f₁ (i₁ z) = f₂ (i₂ z)) →
      ∃ h : (N → R) → L → R, graphOn (J₁ '' X₁ ∪ J₂ '' X₂) h ∈ T.M (N ⊕ L) ∧
        (∀ x ∈ X₁, h (J₁ x) = f₁ x) ∧ (∀ x ∈ X₂, h (J₂ x) = f₂ x) := by
  classical
  have glue : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂, J₁ x₁ = J₂ x₂ ↔ ∃ z ∈ Z, x₁ = i₁ z ∧ x₂ = i₂ z := by
    intro x₁ h₁ x₂ h₂
    constructor
    · intro e
      by_cases hz₁ : ∃ z ∈ Z, x₁ = i₁ z
      · obtain ⟨z, hz, rfl⟩ := hz₁
        exact ⟨z, hz, rfl, hb₂ h₂ (hi₂ hz) (e.symm.trans (ha z hz))⟩
      by_cases hz₂ : ∃ z ∈ Z, x₂ = i₂ z
      · obtain ⟨z, hz, rfl⟩ := hz₂
        exact ⟨z, hz, hb₁ h₁ (hi₁ hz) (e.trans (ha z hz).symm), rfl⟩
      push Not at hz₁ hz₂
      exact absurd e (hc x₁ h₁ hz₁ x₂ h₂ hz₂)
    · rintro ⟨z, hz, rfl, rfl⟩
      exact ha z hz
  refine ⟨(hU N).2 _ (T.image_mem hJ₁) _ (T.image_mem hJ₂), glue, ?_⟩
  intro L _ f₁ f₂ hf₁ hf₂ hf
  let G₁ : (I₁ → R) → N ⊕ L → R := fun x => Sum.elim (J₁ x) (f₁ x)
  let G₂ : (I₂ → R) → N ⊕ L → R := fun x => Sum.elim (J₂ x) (f₂ x)
  have hG₁ : graphOn X₁ G₁ ∈ T.M (I₁ ⊕ (N ⊕ L)) := T.graph_mem_of_coords hX₁ fun k => by
    rcases k with n | l
    · exact T.isTameFun_of_graph hJ₁ n
    · exact T.isTameFun_of_graph hf₁ l
  have hG₂ : graphOn X₂ G₂ ∈ T.M (I₂ ⊕ (N ⊕ L)) := T.graph_mem_of_coords hX₂ fun k => by
    rcases k with n | l
    · exact T.isTameFun_of_graph hJ₂ n
    · exact T.isTameFun_of_graph hf₂ l
  let h : (N → R) → L → R := fun p =>
    if hp : ∃ x ∈ X₁, J₁ x = p then f₁ hp.choose
    else if hp' : ∃ x ∈ X₂, J₂ x = p then f₂ hp'.choose
    else fun _ => Classical.ofNonempty
  have h₁ : ∀ x ∈ X₁, h (J₁ x) = f₁ x := by
    intro x hx
    have hp : ∃ x' ∈ X₁, J₁ x' = J₁ x := ⟨x, hx, rfl⟩
    simp only [h, hp, ↓reduceDIte]
    rw [hb₁ hp.choose_spec.1 hx hp.choose_spec.2]
  have h₂ : ∀ x ∈ X₂, h (J₂ x) = f₂ x := by
    intro x hx
    by_cases hp : ∃ x' ∈ X₁, J₁ x' = J₂ x
    · simp only [h, hp, ↓reduceDIte]
      obtain ⟨z, hz, e₁, e₂⟩ := (glue _ hp.choose_spec.1 x hx).1 hp.choose_spec.2
      rw [e₁, e₂, hf z hz]
    · have hp' : ∃ x' ∈ X₂, J₂ x' = J₂ x := ⟨x, hx, rfl⟩
      simp only [h, hp, hp', ↓reduceDIte]
      rw [hb₂ hp'.choose_spec.1 hx hp'.choose_spec.2]
  refine ⟨h, ?_, h₁, h₂⟩
  convert (hU (N ⊕ L)).2 _ (T.image_mem hG₁) _ (T.image_mem hG₂) using 1
  ext y
  simp only [graphOn, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, ex⟩ | ⟨x, hx, ex⟩, hk⟩
    · refine Or.inl ⟨x, hx, funext fun j => ?_⟩
      rcases j with n | l
      · exact congrFun ex n
      · rw [hk l, ← ex, h₁ x hx]; rfl
    · refine Or.inr ⟨x, hx, funext fun j => ?_⟩
      rcases j with n | l
      · exact congrFun ex n
      · rw [hk l, ← ex, h₂ x hx]; rfl
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨Or.inl ⟨x, hx, rfl⟩, fun l => (congrFun (h₁ x hx) l).symm⟩
    · exact ⟨Or.inr ⟨x, hx, rfl⟩, fun l => (congrFun (h₂ x hx) l).symm⟩

/-- One side of the construction of page 13: for a tame embedding `i : Z ↪ X`, a tame
family `Φ : X → R^K` with `Φ ∘ i = id` ((M7) coordinate by coordinate) and a tame
`F : X → R^A`, `e ∈ R₀^A`, with `i(Z) = F⁻¹(e)` and `F` injective off `i(Z)` ((M6)). -/
theorem side_data [Nonempty R] (h6 : T.M6) (h7 : T.M7) {I K : Type} [Finite I] [Finite K]
    {X : Set (I → R)} {Z : Set (K → R)} (hX : X ∈ T.M I) {i : (K → R) → I → R}
    (hi : graphOn Z i ∈ T.M (K ⊕ I)) (hm : Set.MapsTo i Z X) (hinj : Set.InjOn i Z) :
    ∃ (Φ : (I → R) → K → R) (A : Type) (_ : Finite A) (F : (I → R) → A → R) (e : A → R),
      (∀ k, T.IsTameFun X (fun x => Φ x k)) ∧ (∀ z ∈ Z, Φ (i z) = z) ∧
      graphOn X F ∈ T.M (I ⊕ A) ∧ (∀ a, e a ∈ T.R0) ∧
      (∀ x ∈ X, x ∈ i '' Z ↔ F x = e) ∧ Set.InjOn F (X \ i '' Z) := by
  classical
  have hZ' : i '' Z ∈ T.M I := T.image_mem hi
  have hsub : i '' Z ⊆ X := Set.image_subset_iff.2 hm
  -- the inverse of `i` on `i(Z)`, a tame family
  let inv : (I → R) → K → R := fun x =>
    if h : ∃ z ∈ Z, i z = x then h.choose else fun _ => Classical.ofNonempty
  have inv_spec : ∀ z ∈ Z, inv (i z) = z := by
    intro z hz
    have h : ∃ z' ∈ Z, i z' = i z := ⟨z, hz, rfl⟩
    simp only [inv, h, ↓reduceDIte]
    exact hinj h.choose_spec.1 hz h.choose_spec.2
  have hinv : graphOn (i '' Z) inv ∈ T.M (I ⊕ K) := by
    convert T.m1 (Sum.swap : I ⊕ K → K ⊕ I) hi using 1
    ext y
    simp only [graphOn, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨z, hz, ez⟩, hk⟩
      refine ⟨Sum.elim z (i z), ⟨hz, fun _ => rfl⟩, funext fun j => ?_⟩
      rcases j with j | k
      · exact congrFun ez j
      · simp only [comp_apply, Sum.swap_inr, Sum.elim_inl]
        rw [hk k, ← ez, inv_spec z hz]
    · rintro ⟨y', ⟨hy', hk⟩, rfl⟩
      refine ⟨⟨y' ∘ Sum.inl, hy', funext fun j => (hk j).symm⟩, fun k => ?_⟩
      have e : (y' ∘ Sum.swap) ∘ Sum.inl = i (y' ∘ Sum.inl) := funext fun j => hk j
      rw [e, inv_spec _ hy']
      rfl
  -- (M7), coordinate by coordinate
  have ext : ∀ k : K, ∃ g : (I → R) → R, T.IsTameFun X g ∧ ∀ x ∈ i '' Z, g x = inv x k :=
    fun k => h7 hX hZ' hsub (T.isTameFun_of_graph hinv k)
  choose φ hφ hφZ using ext
  -- (M6)
  obtain ⟨A, hA, F, e, hF, he, hfib, hFinj⟩ := h6 hX hZ' hsub
  refine ⟨fun x k => φ k x, A, hA, F, e, hφ, fun z hz => funext fun k => ?_, hF, he, hfib,
    hFinj⟩
  change φ k (i z) = z k
  rw [hφZ k (i z) ⟨z, hz, rfl⟩, inv_spec z hz]

/-- **Pages 12 and 13, the Proposition.** Under (M5′), (M6) and (M7), two tame embeddings
`i₁ : Z ↪ X₁`, `i₂ : Z ↪ X₂` have a pushout computed as in sets: tame embeddings
`J₁`, `J₂` into some `R^N` (diagram (*): `X₁` on the level `e₂`, `X₂` on the level `e₁`)
whose images meet exactly along `Z`, with tame union, and with the universal property for
tame maps. -/
theorem pushout_exists [Nonempty R] (hU : T.Unions) (h6 : T.M6) (h7 : T.M7)
    {I₁ I₂ K : Type} [Finite I₁] [Finite I₂] [Finite K] {X₁ : Set (I₁ → R)}
    {X₂ : Set (I₂ → R)} {Z : Set (K → R)} (hX₁ : X₁ ∈ T.M I₁) (hX₂ : X₂ ∈ T.M I₂)
    {i₁ : (K → R) → I₁ → R} {i₂ : (K → R) → I₂ → R}
    (hi₁ : graphOn Z i₁ ∈ T.M (K ⊕ I₁)) (hi₂ : graphOn Z i₂ ∈ T.M (K ⊕ I₂))
    (hm₁ : Set.MapsTo i₁ Z X₁) (hm₂ : Set.MapsTo i₂ Z X₂)
    (hinj₁ : Set.InjOn i₁ Z) (hinj₂ : Set.InjOn i₂ Z) :
    ∃ (N : Type) (_ : Finite N) (J₁ : (I₁ → R) → N → R) (J₂ : (I₂ → R) → N → R),
      graphOn X₁ J₁ ∈ T.M (I₁ ⊕ N) ∧ graphOn X₂ J₂ ∈ T.M (I₂ ⊕ N) ∧
      Set.InjOn J₁ X₁ ∧ Set.InjOn J₂ X₂ ∧ (∀ z ∈ Z, J₁ (i₁ z) = J₂ (i₂ z)) ∧
      J₁ '' X₁ ∪ J₂ '' X₂ ∈ T.M N ∧
      (∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂, J₁ x₁ = J₂ x₂ ↔ ∃ z ∈ Z, x₁ = i₁ z ∧ x₂ = i₂ z) ∧
      ∀ (L : Type) [Finite L] (f₁ : (I₁ → R) → L → R) (f₂ : (I₂ → R) → L → R),
        graphOn X₁ f₁ ∈ T.M (I₁ ⊕ L) → graphOn X₂ f₂ ∈ T.M (I₂ ⊕ L) →
        (∀ z ∈ Z, f₁ (i₁ z) = f₂ (i₂ z)) →
        ∃ h : (N → R) → L → R, graphOn (J₁ '' X₁ ∪ J₂ '' X₂) h ∈ T.M (N ⊕ L) ∧
          (∀ x ∈ X₁, h (J₁ x) = f₁ x) ∧ (∀ x ∈ X₂, h (J₂ x) = f₂ x) := by
  obtain ⟨Φ₁, A₁, _, F₁, e₁, hΦ₁, hΦ₁Z, hF₁, he₁, hfib₁, hinjF₁⟩ :=
    T.side_data h6 h7 hX₁ hi₁ hm₁ hinj₁
  obtain ⟨Φ₂, A₂, _, F₂, e₂, hΦ₂, hΦ₂Z, hF₂, he₂, hfib₂, hinjF₂⟩ :=
    T.side_data h6 h7 hX₂ hi₂ hm₂ hinj₂
  let J₁ : (I₁ → R) → K ⊕ (A₁ ⊕ A₂) → R := fun x => Sum.elim (Φ₁ x) (Sum.elim (F₁ x) e₂)
  let J₂ : (I₂ → R) → K ⊕ (A₁ ⊕ A₂) → R := fun x => Sum.elim (Φ₂ x) (Sum.elim e₁ (F₂ x))
  have hJ₁ : graphOn X₁ J₁ ∈ T.M (I₁ ⊕ (K ⊕ (A₁ ⊕ A₂))) := T.graph_mem_of_coords hX₁ fun j => by
    rcases j with k | a | a
    · exact hΦ₁ k
    · exact T.isTameFun_of_graph hF₁ a
    · exact T.isTameFun_const hX₁ (he₂ a)
  have hJ₂ : graphOn X₂ J₂ ∈ T.M (I₂ ⊕ (K ⊕ (A₁ ⊕ A₂))) := T.graph_mem_of_coords hX₂ fun j => by
    rcases j with k | a | a
    · exact hΦ₂ k
    · exact T.isTameFun_const hX₂ (he₁ a)
    · exact T.isTameFun_of_graph hF₂ a
  -- `F_j ∘ i_j = e_j`
  have hFZ₁ : ∀ z ∈ Z, F₁ (i₁ z) = e₁ := fun z hz => (hfib₁ _ (hm₁ hz)).1 ⟨z, hz, rfl⟩
  have hFZ₂ : ∀ z ∈ Z, F₂ (i₂ z) = e₂ := fun z hz => (hfib₂ _ (hm₂ hz)).1 ⟨z, hz, rfl⟩
  have ha : ∀ z ∈ Z, J₁ (i₁ z) = J₂ (i₂ z) := by
    intro z hz
    funext j
    rcases j with k | a | a
    · simp only [J₁, J₂, Sum.elim_inl, hΦ₁Z z hz, hΦ₂Z z hz]
    · simp only [J₁, J₂, Sum.elim_inr, Sum.elim_inl, hFZ₁ z hz]
    · simp only [J₁, J₂, Sum.elim_inr, hFZ₂ z hz]
  -- injectivity of each side
  have inj : ∀ {I A : Type} {X : Set (I → R)} {i : (K → R) → I → R} {Φ : (I → R) → K → R}
      {F : (I → R) → A → R} {e : A → R}, (∀ z ∈ Z, Φ (i z) = z) →
      (∀ x ∈ X, x ∈ i '' Z ↔ F x = e) → Set.InjOn F (X \ i '' Z) →
      ∀ x ∈ X, ∀ x' ∈ X, Φ x = Φ x' → F x = F x' → x = x' := by
    intro I A X i Φ F e hΦZ hfib hinjF x hx x' hx' eΦ eF
    by_cases hZx : x ∈ i '' Z
    · have hZx' : x' ∈ i '' Z := (hfib x' hx').2 (eF ▸ (hfib x hx).1 hZx)
      obtain ⟨z, hz, rfl⟩ := hZx
      obtain ⟨z', hz', rfl⟩ := hZx'
      rw [hΦZ z hz, hΦZ z' hz'] at eΦ
      rw [eΦ]
    · have hZx' : x' ∉ i '' Z := fun h => hZx ((hfib x hx).2 (eF.trans ((hfib x' hx').1 h)))
      exact hinjF ⟨hx, hZx⟩ ⟨hx', hZx'⟩ eF
  have hb₁ : Set.InjOn J₁ X₁ := fun x hx x' hx' e =>
    inj hΦ₁Z hfib₁ hinjF₁ x hx x' hx' (funext fun k => congrFun e (.inl k))
      (funext fun a => congrFun e (.inr (.inl a)))
  have hb₂ : Set.InjOn J₂ X₂ := fun x hx x' hx' e =>
    inj hΦ₂Z hfib₂ hinjF₂ x hx x' hx' (funext fun k => congrFun e (.inl k))
      (funext fun a => congrFun e (.inr (.inr a)))
  have hc : ∀ x₁ ∈ X₁, (∀ z ∈ Z, x₁ ≠ i₁ z) → ∀ x₂ ∈ X₂, (∀ z ∈ Z, x₂ ≠ i₂ z) →
      J₁ x₁ ≠ J₂ x₂ := by
    intro x₁ hx₁ hz₁ x₂ _ _ e
    obtain ⟨z, hz, ez⟩ := (hfib₁ x₁ hx₁).2 (funext fun a => congrFun e (.inr (.inl a)))
    exact hz₁ z hz ez.symm
  obtain ⟨hP, hglue, huniv⟩ :=
    T.pushout_of_criterion hU hX₁ hX₂ hm₁ hm₂ hJ₁ hJ₂ ha hb₁ hb₂ hc
  exact ⟨_, inferInstance, J₁, J₂, hJ₁, hJ₂, hb₁, hb₂, ha, hP, hglue, huniv⟩


/-! ### Necessity of the criterion of page 10

« Inversement, si la somme existe et que l'oubli la respecte, un plongement `F : X ↪ R^A`
donne `f = F ∘ g₁` et `g = F ∘ g₂`. » Here the pushout is a tame `P ⊂ R^N` with tame `q₁`,
`q₂`, so `F` is the inclusion of `P`, and « the forgetful functor respects it » is the
set-theoretic universal property `IsSetPushout`. -/

/-- The cocone `q₁ : X₁ → P`, `q₂ : X₂ → P` under `X₁ ← Z → X₂` is a pushout in sets: it
commutes, `P` is the union of the two images, and every pair of maps to a non-empty set `S`
compatible on `Z` factors through it (uniquely on `P`, since `P` is covered). -/
def IsSetPushout {I₁ I₂ K N : Type} (Z : Set (K → R)) (X₁ : Set (I₁ → R))
    (X₂ : Set (I₂ → R)) (i₁ : (K → R) → I₁ → R) (i₂ : (K → R) → I₂ → R) (P : Set (N → R))
    (q₁ : (I₁ → R) → N → R) (q₂ : (I₂ → R) → N → R) : Prop :=
  (∀ z ∈ Z, q₁ (i₁ z) = q₂ (i₂ z)) ∧ P = q₁ '' X₁ ∪ q₂ '' X₂ ∧
    ∀ (S : Type) [Nonempty S] (u₁ : (I₁ → R) → S) (u₂ : (I₂ → R) → S),
      (∀ z ∈ Z, u₁ (i₁ z) = u₂ (i₂ z)) →
      ∃ u : (N → R) → S, (∀ x ∈ X₁, u (q₁ x) = u₁ x) ∧ ∀ x ∈ X₂, u (q₂ x) = u₂ x

/-- **The criterion of page 10, necessity.** If `i₁`, `i₂` are injective on `Z` and a tame
cocone `q₁`, `q₂` into `P ⊂ R^N` is a pushout in sets, the coordinates of `q₁`, `q₂` are tame
functions satisfying a), b), c). Neither (M5′), (M6), (M7) nor the tameness of `P` is used;
c) holds in the stronger form `q₁ x₁ = q₂ x₂ → x₂ ∈ i₂(Z)`. -/
theorem criterion_of_pushout {I₁ I₂ K N : Type} [Finite I₁] [Finite I₂] [Finite N]
    {X₁ : Set (I₁ → R)} {X₂ : Set (I₂ → R)} {Z : Set (K → R)}
    {i₁ : (K → R) → I₁ → R} {i₂ : (K → R) → I₂ → R}
    (hinj₁ : Set.InjOn i₁ Z) (hinj₂ : Set.InjOn i₂ Z) {P : Set (N → R)}
    {q₁ : (I₁ → R) → N → R} {q₂ : (I₂ → R) → N → R}
    (hq₁ : graphOn X₁ q₁ ∈ T.M (I₁ ⊕ N)) (hq₂ : graphOn X₂ q₂ ∈ T.M (I₂ ⊕ N))
    (hP : IsSetPushout Z X₁ X₂ i₁ i₂ P q₁ q₂) :
    (∀ n, T.IsTameFun X₁ (fun x => q₁ x n)) ∧ (∀ n, T.IsTameFun X₂ (fun x => q₂ x n)) ∧
    (∀ z ∈ Z, q₁ (i₁ z) = q₂ (i₂ z)) ∧ Set.InjOn q₁ X₁ ∧ Set.InjOn q₂ X₂ ∧
    ∀ x₁ ∈ X₁, (∀ z ∈ Z, x₁ ≠ i₁ z) → ∀ x₂ ∈ X₂, (∀ z ∈ Z, x₂ ≠ i₂ z) →
      q₁ x₁ ≠ q₂ x₂ := by
  obtain ⟨ha, -, hU⟩ := hP
  refine ⟨T.isTameFun_of_graph hq₁, T.isTameFun_of_graph hq₂, ha, ?_, ?_, ?_⟩
  · intro x hx x' hx' e
    obtain ⟨u, hu, -⟩ := hU Prop (fun y => y = x) (fun y => ∃ z ∈ Z, y = i₂ z ∧ i₁ z = x)
      fun z hz => propext ⟨fun h => ⟨z, hz, rfl, h⟩, fun ⟨z', hz', e', h⟩ => by
        rw [hinj₂ hz hz' e']; exact h⟩
    exact (cast ((e ▸ hu x hx).symm.trans (hu x' hx')) rfl).symm
  · intro x hx x' hx' e
    obtain ⟨u, -, hu⟩ := hU Prop (fun y => ∃ z ∈ Z, y = i₁ z ∧ i₂ z = x) (fun y => y = x)
      fun z hz => propext ⟨fun ⟨z', hz', e', h⟩ => by rw [hinj₁ hz hz' e']; exact h,
        fun h => ⟨z, hz, rfl, h⟩⟩
    exact (cast ((e ▸ hu x hx).symm.trans (hu x' hx')) rfl).symm
  · intro x₁ hx₁ _ x₂ hx₂ hz₂ e
    obtain ⟨u, hu₁, hu₂⟩ := hU Prop (fun _ => True) (fun y => ∃ z ∈ Z, y = i₂ z)
      fun z hz => propext ⟨fun _ => ⟨z, hz, rfl⟩, fun _ => trivial⟩
    obtain ⟨z, hz, ez⟩ := cast ((e ▸ hu₁ x₁ hx₁).symm.trans (hu₂ x₂ hx₂)) trivial
    exact hz₂ z hz ez

/-- **The criterion of pages 10 and 11**, both directions, for tame embeddings `i₁`, `i₂`
under (M5′): there are tame families `f`, `g` satisfying a), b), c) iff there is a tame
`P ⊂ R^N` with a tame cocone which is a pushout in sets (the forgetful functor respects it)
and has the universal property for tame maps (the pushout exists in tame spaces). -/
theorem criterion_iff [Nonempty R] (hU : T.Unions) {I₁ I₂ K : Type} [Finite I₁] [Finite I₂]
    {X₁ : Set (I₁ → R)} {X₂ : Set (I₂ → R)} {Z : Set (K → R)}
    (hX₁ : X₁ ∈ T.M I₁) (hX₂ : X₂ ∈ T.M I₂) {i₁ : (K → R) → I₁ → R} {i₂ : (K → R) → I₂ → R}
    (hm₁ : Set.MapsTo i₁ Z X₁) (hm₂ : Set.MapsTo i₂ Z X₂)
    (hinj₁ : Set.InjOn i₁ Z) (hinj₂ : Set.InjOn i₂ Z) :
    (∃ (A : Type) (_ : Finite A) (f : (I₁ → R) → A → R) (g : (I₂ → R) → A → R),
      graphOn X₁ f ∈ T.M (I₁ ⊕ A) ∧ graphOn X₂ g ∈ T.M (I₂ ⊕ A) ∧
      (∀ z ∈ Z, f (i₁ z) = g (i₂ z)) ∧ Set.InjOn f X₁ ∧ Set.InjOn g X₂ ∧
      ∀ x₁ ∈ X₁, (∀ z ∈ Z, x₁ ≠ i₁ z) → ∀ x₂ ∈ X₂, (∀ z ∈ Z, x₂ ≠ i₂ z) → f x₁ ≠ g x₂) ↔
    ∃ (N : Type) (_ : Finite N) (P : Set (N → R)) (q₁ : (I₁ → R) → N → R)
      (q₂ : (I₂ → R) → N → R), P ∈ T.M N ∧ graphOn X₁ q₁ ∈ T.M (I₁ ⊕ N) ∧
      graphOn X₂ q₂ ∈ T.M (I₂ ⊕ N) ∧ IsSetPushout Z X₁ X₂ i₁ i₂ P q₁ q₂ ∧
      ∀ (L : Type) [Finite L] (f₁ : (I₁ → R) → L → R) (f₂ : (I₂ → R) → L → R),
        graphOn X₁ f₁ ∈ T.M (I₁ ⊕ L) → graphOn X₂ f₂ ∈ T.M (I₂ ⊕ L) →
        (∀ z ∈ Z, f₁ (i₁ z) = f₂ (i₂ z)) →
        ∃ h : (N → R) → L → R, graphOn P h ∈ T.M (N ⊕ L) ∧
          (∀ x ∈ X₁, h (q₁ x) = f₁ x) ∧ (∀ x ∈ X₂, h (q₂ x) = f₂ x) := by
  classical
  constructor
  · rintro ⟨A, _, f, g, hf, hg, ha, hb₁, hb₂, hc⟩
    obtain ⟨hP, glue, huniv⟩ := T.pushout_of_criterion hU hX₁ hX₂ hm₁ hm₂ hf hg ha hb₁ hb₂ hc
    refine ⟨A, inferInstance, _, f, g, hP, hf, hg, ⟨ha, rfl, ?_⟩, huniv⟩
    intro S _ u₁ u₂ hu
    let u : (A → R) → S := fun p =>
      if hp : ∃ x ∈ X₁, f x = p then u₁ hp.choose
      else if hp' : ∃ x ∈ X₂, g x = p then u₂ hp'.choose else Classical.ofNonempty
    refine ⟨u, fun x hx => ?_, fun x hx => ?_⟩
    · have hp : ∃ x' ∈ X₁, f x' = f x := ⟨x, hx, rfl⟩
      simp only [u, hp, ↓reduceDIte]
      rw [hb₁ hp.choose_spec.1 hx hp.choose_spec.2]
    · by_cases hp : ∃ x' ∈ X₁, f x' = g x
      · simp only [u, hp, ↓reduceDIte]
        obtain ⟨z, hz, e₁, e₂⟩ := (glue _ hp.choose_spec.1 x hx).1 hp.choose_spec.2
        rw [e₁, e₂, hu z hz]
      · have hp' : ∃ x' ∈ X₂, g x' = g x := ⟨x, hx, rfl⟩
        simp only [u, hp, hp', ↓reduceDIte]
        rw [hb₂ hp'.choose_spec.1 hx hp'.choose_spec.2]
  · rintro ⟨N, _, P, q₁, q₂, -, hq₁, hq₂, hP, -⟩
    obtain ⟨-, -, ha, hb₁, hb₂, hc⟩ := T.criterion_of_pushout hinj₁ hinj₂ hq₁ hq₂ hP
    exact ⟨N, inferInstance, q₁, q₂, hq₁, hq₂, ha, hb₁, hb₂, hc⟩

end TameModel

end Grothendieck.Folder120
