module

public import Mathlib

@[expose] public section


/-!
# Folder 67, page 90: modules with an involution and triples `(P, Q, m)`

The modernised reading `transcripts/67/67.modern.tex` (« Modules munis d'une
involution », pages 90, 91 and 99) states, for a `k`-module `M` on which
multiplication by `2` is injective and an involution `σ` of `M`, with
`P = M₊ = Ker(1 - σ)` and `Q = M₋ = Ker(1 + σ)`:

> `P ∩ Q = 0`, `2P ⊕ 2Q ⊂ M' = 2M ⊂ P ⊕ Q`, so `M'` is the preimage of a
> submodule `m ⊂ P/2P ⊕ Q/2Q`, which meets `P/2P` and `Q/2Q` trivially.
> Conversely `(M, σ)` is rebuilt from `(P, Q, m)`.
>
> **Proposition.** The functor `(M, σ) ↦ (P, Q, m)` is an equivalence between
> the category of `2`-regular modules with an involution and that of triples
> formed of two `2`-regular modules and a submodule `m` of `P/2P ⊕ Q/2Q`
> meeting each of the two factors trivially.

This is finding `67-involution-modules-triples` of `src/content/findings.ts`.
Proving it says only that the claim holds as stated; whether it stands in the
literature is a separate question.

What is formalised, for any ring `k` (not necessarily commutative) and with no
finiteness or projectivity hypothesis:

* the two categories, `InvMod k` and `Triple k`;
* the reconstruction functor `build : Triple k ⥤ InvMod k`,
  `(P, Q, m) ↦ (preimage of m in P × Q, id × (-id))`;
* `build` is faithful, full and essentially surjective, hence an equivalence
  (`equivalence : Triple k ≌ InvMod k`);
* `InvMod.essSurj_witness`: every `(M, σ)` is isomorphic to `build` of the
  explicit triple `(M₊, M₋, m)` of the page (`InvMod.triple`), so that the
  inverse of the equivalence sends `(M, σ)` to a triple isomorphic to
  `(M₊, M₋, m)` (`inverse_obj_iso`): this inverse is the page's functor
  `(M, σ) ↦ (P, Q, m)`;
* the facts of the page on the way: `P ∩ Q = 0` (`InvMod.inf_eigen_eq_bot`),
  `M₊ ∩ 2M = 2M₊` and `M₋ ∩ 2M = 2M₋` (`InvMod.mem_two_of_plus`,
  `InvMod.mem_two_of_minus`), and the description of `m` by its preimage:
  `(p̄, q̄) ∈ m ↔ p + q ∈ 2M` (`InvMod.mk_mem_m_iff`).

A submodule of `P/2P × Q/2Q` over `k` is the same as one over `k/2k`, since
`2` kills the product; the file works over `k`. A morphism of triples is a pair
`(f, g)` with `(f̄ × ḡ)(m) ⊂ m'`, stated on representatives.
-/

namespace Grothendieck.Folder67

open CategoryTheory

universe v u

variable (k : Type u) [Ring k]

section Basics

variable {k}
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- `M` is `2`-regular: multiplication by `2` is injective. -/
def TwoRegular (M : Type*) [AddCommGroup M] : Prop :=
  ∀ x : M, 2 • x = 0 → x = 0

/-- The linear map `x ↦ 2x`. -/
def twice (k : Type u) [Ring k] (M : Type*) [AddCommGroup M] [Module k M] : M →ₗ[k] M :=
  (2 : ℕ) • LinearMap.id

@[simp] lemma twice_apply (x : M) : twice k M x = 2 • x := rfl

/-- The submodule `2M`. -/
abbrev two (k : Type u) [Ring k] (M : Type*) [AddCommGroup M] [Module k M] : Submodule k M :=
  LinearMap.range (twice k M)

lemma mem_two {x : M} : x ∈ two k M ↔ ∃ y, 2 • y = x := by
  simp [two]

lemma two_smul_mem_two (y : M) : 2 • y ∈ two k M := mem_two.2 ⟨y, rfl⟩

lemma TwoRegular.cancel (h : TwoRegular M) {a b : M} (e : 2 • a = 2 • b) : a = b :=
  sub_eq_zero.1 (h _ (by rw [smul_sub, e, sub_self]))

lemma TwoRegular.injective (h : TwoRegular M) : Function.Injective (twice k M) :=
  fun _ _ e => h.cancel e

lemma TwoRegular.submodule (h : TwoRegular M) (N : Submodule k M) : TwoRegular N :=
  fun x hx => Subtype.ext (h _ (by simpa using congrArg Subtype.val hx))

/-- Division by `2`, the inverse of `M ≃ 2M`, `y ↦ 2y`. -/
noncomputable def half (h : TwoRegular M) : two k M ≃ₗ[k] M :=
  (LinearEquiv.ofInjective (twice k M) h.injective).symm

lemma two_smul_half (h : TwoRegular M) (x : two k M) : 2 • half h x = (x : M) :=
  congrArg Subtype.val ((LinearEquiv.ofInjective (twice k M) h.injective).apply_symm_apply x)

/-- In `M/2M`, `-x` and `x` have the same class. -/
lemma mk_neg (x : M) :
    (Submodule.Quotient.mk (-x) : M ⧸ two k M) = Submodule.Quotient.mk x := by
  rw [Submodule.Quotient.eq, mem_two]
  exact ⟨-x, by rw [two_nsmul]; abel⟩

lemma neg_mk (x : M) :
    -(Submodule.Quotient.mk x : M ⧸ two k M) = Submodule.Quotient.mk x := by
  rw [← Submodule.Quotient.mk_neg, mk_neg]

lemma mk_two_smul (x : M) :
    (Submodule.Quotient.mk (2 • x) : M ⧸ two k M) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (two_smul_mem_two x)

end Basics

/-! ## The two categories -/

/-- A `2`-regular `k`-module with an involution. -/
structure InvMod where
  /-- the module `M` -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- the involution -/
  σ : carrier →ₗ[k] carrier
  σ_σ : ∀ x, σ (σ x) = x
  reg : TwoRegular carrier

attribute [instance] InvMod.isAddCommGroup InvMod.isModule

namespace InvMod

variable {k}

/-- Morphisms: `k`-linear maps commuting with the involutions. -/
@[ext]
structure Hom (X Y : InvMod.{v} k) where
  /-- the underlying linear map -/
  f : X.carrier →ₗ[k] Y.carrier
  comm : ∀ x, f (X.σ x) = Y.σ (f x)

instance : Category (InvMod.{v} k) where
  Hom := Hom
  id X := ⟨LinearMap.id, fun _ => rfl⟩
  comp φ ψ := ⟨ψ.f ∘ₗ φ.f, fun x => by simp [φ.comm, ψ.comm]⟩

@[ext]
lemma hom_ext {X Y : InvMod.{v} k} {φ ψ : X ⟶ Y} (h : Hom.f φ = Hom.f ψ) : φ = ψ :=
  Hom.ext h

@[simp] lemma id_f (X : InvMod.{v} k) : Hom.f (𝟙 X) = LinearMap.id := rfl

@[simp] lemma comp_f {X Y Z : InvMod.{v} k} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    Hom.f (φ ≫ ψ) = Hom.f ψ ∘ₗ Hom.f φ := rfl

/-- A morphism whose underlying map is bijective is an isomorphism. -/
noncomputable def isoOfBijective {X Y : InvMod.{v} k} (φ : X ⟶ Y)
    (hb : Function.Bijective (Hom.f φ)) : X ≅ Y where
  hom := φ
  inv :=
    { f := (LinearEquiv.ofBijective (Hom.f φ) hb).symm.toLinearMap
      comm := fun y => by
        set e := LinearEquiv.ofBijective (Hom.f φ) hb
        have he : ∀ a, Hom.f φ (e.symm a) = a := fun a => e.apply_symm_apply a
        apply hb.1
        simp only [LinearEquiv.coe_coe]
        rw [Hom.comm φ, he, he] }
  hom_inv_id := by
    ext x
    exact (LinearEquiv.ofBijective (Hom.f φ) hb).symm_apply_apply x
  inv_hom_id := by
    ext y
    exact (LinearEquiv.ofBijective (Hom.f φ) hb).apply_symm_apply y

/-- The `+1`-eigenmodule `M₊ = Ker(1 - σ)`. -/
def plus (X : InvMod.{v} k) : Submodule k X.carrier := LinearMap.ker (LinearMap.id - X.σ)

/-- The `-1`-eigenmodule `M₋ = Ker(1 + σ)`. -/
def minus (X : InvMod.{v} k) : Submodule k X.carrier := LinearMap.ker (LinearMap.id + X.σ)

variable (X : InvMod.{v} k)

lemma mem_plus {x : X.carrier} : x ∈ X.plus ↔ X.σ x = x := by
  rw [plus, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, eq_comm]

lemma mem_minus {x : X.carrier} : x ∈ X.minus ↔ X.σ x = -x := by
  rw [minus, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_neg_eq, eq_comm]

/-- Page 90: `P ∩ Q = 0`, from `2`-regularity. -/
theorem inf_eigen_eq_bot : X.plus ⊓ X.minus = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hx
  rw [mem_plus] at h1
  rw [mem_minus, h1] at h2
  refine (Submodule.mem_bot k).2 (X.reg x ?_)
  rw [two_nsmul, ← neg_add_cancel x, ← h2]

/-- Page 90: `2x = (x + σx) + (x - σx)`, with `x + σx ∈ M₊` and `x - σx ∈ M₋`. -/
lemma add_σ_mem_plus (x : X.carrier) : x + X.σ x ∈ X.plus := by
  rw [mem_plus, map_add, X.σ_σ, add_comm]

lemma sub_σ_mem_minus (x : X.carrier) : x - X.σ x ∈ X.minus := by
  rw [mem_minus, map_sub, X.σ_σ, neg_sub]

/-- Page 90: `M₊ ∩ 2M = 2M₊` (« de `2x ∈ P` on tire `x ∈ P` »). -/
theorem mem_two_of_plus (p : X.plus) (h : (p : X.carrier) ∈ two k X.carrier) :
    p ∈ two k X.plus := by
  obtain ⟨y, hy⟩ := mem_two.1 h
  have hp := (X.mem_plus).1 p.2
  have hy' : y ∈ X.plus := by
    rw [mem_plus]
    apply X.reg.cancel
    rw [← map_nsmul, hy, hp]
  exact mem_two.2 ⟨⟨y, hy'⟩, Subtype.ext (by simpa using hy)⟩

/-- Page 90: `M₋ ∩ 2M = 2M₋`. -/
theorem mem_two_of_minus (q : X.minus) (h : (q : X.carrier) ∈ two k X.carrier) :
    q ∈ two k X.minus := by
  obtain ⟨y, hy⟩ := mem_two.1 h
  have hq := (X.mem_minus).1 q.2
  have hy' : y ∈ X.minus := by
    rw [mem_minus]
    apply X.reg.cancel
    rw [← map_nsmul, hy, hq, ← hy, smul_neg]
  exact mem_two.2 ⟨⟨y, hy'⟩, Subtype.ext (by simpa using hy)⟩

end InvMod

/-- A triple `(P, Q, m)`: two `2`-regular modules and a submodule
`m ⊂ P/2P × Q/2Q` meeting each factor trivially. -/
structure Triple where
  /-- the module `P` -/
  P : Type v
  /-- the module `Q` -/
  Q : Type v
  [gP : AddCommGroup P]
  [mP : Module k P]
  [gQ : AddCommGroup Q]
  [mQ : Module k Q]
  regP : TwoRegular P
  regQ : TwoRegular Q
  /-- the submodule `m` -/
  m : Submodule k ((P ⧸ two k P) × (Q ⧸ two k Q))
  m_P : ∀ p : P ⧸ two k P, (p, 0) ∈ m → p = 0
  m_Q : ∀ q : Q ⧸ two k Q, (0, q) ∈ m → q = 0

attribute [instance] Triple.gP Triple.mP Triple.gQ Triple.mQ

namespace Triple

variable {k}

/-- Morphisms of triples: pairs `(f, g)` with `(f̄ × ḡ)(m) ⊂ m'`. -/
@[ext]
structure Hom (X Y : Triple.{v} k) where
  /-- the map on `P` -/
  f : X.P →ₗ[k] Y.P
  /-- the map on `Q` -/
  g : X.Q →ₗ[k] Y.Q
  hm : ∀ p q, (Submodule.Quotient.mk p, Submodule.Quotient.mk q) ∈ X.m →
    (Submodule.Quotient.mk (f p), Submodule.Quotient.mk (g q)) ∈ Y.m

instance : Category (Triple.{v} k) where
  Hom := Hom
  id X := ⟨LinearMap.id, LinearMap.id, fun _ _ h => h⟩
  comp φ ψ := ⟨ψ.f ∘ₗ φ.f, ψ.g ∘ₗ φ.g, fun p q h => ψ.hm _ _ (φ.hm p q h)⟩

@[ext]
lemma hom_ext {X Y : Triple.{v} k} {φ ψ : X ⟶ Y} (h1 : Hom.f φ = Hom.f ψ)
    (h2 : Hom.g φ = Hom.g ψ) : φ = ψ :=
  Hom.ext h1 h2

/-- The preimage `N ⊂ P × Q` of `m`. -/
def N (X : Triple.{v} k) : Submodule k (X.P × X.Q) :=
  X.m.comap ((two k X.P).mkQ.prodMap (two k X.Q).mkQ)

lemma mem_N {X : Triple.{v} k} {z : X.P × X.Q} :
    z ∈ X.N ↔ (Submodule.Quotient.mk z.1, Submodule.Quotient.mk z.2) ∈ X.m := Iff.rfl

lemma two_smul_inl_mem (X : Triple.{v} k) (p : X.P) : ((2 • p, 0) : X.P × X.Q) ∈ X.N := by
  rw [mem_N]; simp only [mk_two_smul, Submodule.Quotient.mk_zero]; exact X.m.zero_mem

lemma two_smul_inr_mem (X : Triple.{v} k) (q : X.Q) : ((0, 2 • q) : X.P × X.Q) ∈ X.N := by
  rw [mem_N]; simp only [mk_two_smul, Submodule.Quotient.mk_zero]; exact X.m.zero_mem

/-! ## The reconstruction functor -/

/-- The involution `id × (-id)` of `N`. -/
def σN (X : Triple.{v} k) : X.N →ₗ[k] X.N :=
  (LinearMap.prodMap LinearMap.id (-LinearMap.id)).restrict (p := X.N) (q := X.N)
    (fun z hz => by
      rw [mem_N] at hz ⊢
      simpa [neg_mk] using hz)

@[simp] lemma σN_apply (X : Triple.{v} k) (z : X.N) :
    ((X.σN z : X.N) : X.P × X.Q) = ((z : X.P × X.Q).1, -(z : X.P × X.Q).2) := rfl

/-- `(P, Q, m) ↦ (N, id × (-id))`, the module of page 90 rebuilt from the triple. -/
def buildObj (X : Triple.{v} k) : InvMod.{v} k where
  carrier := X.N
  σ := X.σN
  σ_σ z := Subtype.ext (by simp)
  reg z hz := by
    have h := congrArg Subtype.val hz
    exact Subtype.ext (Prod.ext (X.regP _ (congrArg Prod.fst h)) (X.regQ _ (congrArg Prod.snd h)))

/-- The linear map `N → N'` induced by a morphism of triples. -/
def bmap {X Y : Triple.{v} k} (φ : X ⟶ Y) : X.N →ₗ[k] Y.N :=
  (LinearMap.prodMap (Hom.f φ) (Hom.g φ)).restrict (p := X.N) (q := Y.N)
    (fun z hz => Hom.hm φ z.1 z.2 hz)

@[simp] lemma bmap_apply {X Y : Triple.{v} k} (φ : X ⟶ Y) (z : X.N) :
    ((bmap φ z : Y.N) : Y.P × Y.Q) =
      (Hom.f φ (z : X.P × X.Q).1, Hom.g φ (z : X.P × X.Q).2) := rfl

/-- The map of rebuilt modules induced by a morphism of triples. -/
def buildMap {X Y : Triple.{v} k} (φ : X ⟶ Y) : buildObj X ⟶ buildObj Y where
  f := bmap φ
  comm z := by
    change bmap φ (X.σN z) = Y.σN (bmap φ z)
    exact Subtype.ext (Prod.ext rfl (map_neg (Hom.g φ) _))

end Triple

/-- The functor `(P, Q, m) ↦ (M, σ)` of page 90. -/
def build : Triple.{v} k ⥤ InvMod.{v} k where
  obj := Triple.buildObj
  map := Triple.buildMap
  map_id _ := rfl
  map_comp _ _ := rfl

namespace Triple

variable {k}

instance : (build k).Faithful where
  map_injective {X Y} φ ψ h := by
    have key : ∀ z : X.N, ((bmap φ z : Y.N) : Y.P × Y.Q) = ((bmap ψ z : Y.N) : Y.P × Y.Q) :=
      fun z => congr(Subtype.val (InvMod.Hom.f $h z))
    ext p
    · have h1 := congrArg Prod.fst (key ⟨_, X.two_smul_inl_mem p⟩)
      simp only [bmap_apply, map_nsmul] at h1
      exact Y.regP.cancel h1
    · have h1 := congrArg Prod.snd (key ⟨_, X.two_smul_inr_mem p⟩)
      simp only [bmap_apply, map_nsmul] at h1
      exact Y.regQ.cancel h1

section Full

variable {X Y : Triple.{v} k} (h : buildObj X ⟶ buildObj Y)

/-- `p ↦ 2p`, into `N`. -/
def ιP (X : Triple.{v} k) : X.P →ₗ[k] X.N :=
  LinearMap.codRestrict X.N (LinearMap.inl k X.P X.Q ∘ₗ twice k X.P)
    (fun p => by simpa using X.two_smul_inl_mem p)

/-- `q ↦ 2q`, into `N`. -/
def ιQ (X : Triple.{v} k) : X.Q →ₗ[k] X.N :=
  LinearMap.codRestrict X.N (LinearMap.inr k X.P X.Q ∘ₗ twice k X.Q)
    (fun q => by simpa using X.two_smul_inr_mem q)

@[simp] lemma ιP_apply (p : X.P) : ((ιP X p : X.N) : X.P × X.Q) = (2 • p, 0) := rfl
@[simp] lemma ιQ_apply (q : X.Q) : ((ιQ X q : X.N) : X.P × X.Q) = (0, 2 • q) := rfl

/-- The underlying linear map `N → N'` of `h`. -/
def hh : X.N →ₗ[k] Y.N := InvMod.Hom.f h

lemma hh_comm (z : X.N) : hh h (X.σN z) = Y.σN (hh h z) := InvMod.Hom.comm h z

/-- `p ↦ h(2p, 0)`, first coordinate. -/
def aP : X.P →ₗ[k] Y.P :=
  LinearMap.fst k Y.P Y.Q ∘ₗ Y.N.subtype ∘ₗ hh h ∘ₗ ιP X

/-- `q ↦ h(0, 2q)`, second coordinate. -/
def aQ : X.Q →ₗ[k] Y.Q :=
  LinearMap.snd k Y.P Y.Q ∘ₗ Y.N.subtype ∘ₗ hh h ∘ₗ ιQ X

lemma aP_apply (p : X.P) : aP h p = ((hh h (ιP X p) : Y.N) : Y.P × Y.Q).1 := rfl

lemma aQ_apply (q : X.Q) : aQ h q = ((hh h (ιQ X q) : Y.N) : Y.P × Y.Q).2 := rfl

/-- `h(2p, 0)` lies in `2P' × 0`: it is fixed by `σ`, hence its second
coordinate vanishes, and `m'` meets `P'/2P'` trivially. -/
lemma image_ιP (p : X.P) :
    ((hh h (ιP X p) : Y.N) : Y.P × Y.Q).2 = 0 ∧ aP h p ∈ two k Y.P := by
  have hfix : X.σN (ιP X p) = ιP X p := Subtype.ext (by simp)
  have hc := hh_comm h (ιP X p)
  rw [hfix] at hc
  rw [aP_apply]
  generalize hh h (ιP X p) = w at hc ⊢
  obtain ⟨⟨a, b⟩, hw⟩ := w
  have hb : b = -b := congrArg (fun w : Y.N => (w : Y.P × Y.Q).2) hc
  have h2 : b = 0 := Y.regQ _ (by rw [two_nsmul, ← add_neg_cancel b, ← hb])
  refine ⟨h2, ?_⟩
  have hmem : (Submodule.Quotient.mk a, Submodule.Quotient.mk b) ∈ Y.m := hw
  rw [h2, Submodule.Quotient.mk_zero] at hmem
  exact (Submodule.Quotient.mk_eq_zero _).1 (Y.m_P _ hmem)

/-- `h(0, 2q)` lies in `0 × 2Q'`. -/
lemma image_ιQ (q : X.Q) :
    ((hh h (ιQ X q) : Y.N) : Y.P × Y.Q).1 = 0 ∧ aQ h q ∈ two k Y.Q := by
  have hfix : X.σN (ιQ X q) = -ιQ X q := Subtype.ext (by simp)
  have hc := hh_comm h (ιQ X q)
  rw [hfix, map_neg] at hc
  rw [aQ_apply]
  generalize hh h (ιQ X q) = w at hc ⊢
  obtain ⟨⟨a, b⟩, hw⟩ := w
  have ha : -a = a := congrArg (fun w : Y.N => (w : Y.P × Y.Q).1) hc
  have h1 : a = 0 := Y.regP _ (by rw [two_nsmul, ← neg_add_cancel a, ha])
  refine ⟨h1, ?_⟩
  have hmem : (Submodule.Quotient.mk a, Submodule.Quotient.mk b) ∈ Y.m := hw
  rw [h1, Submodule.Quotient.mk_zero] at hmem
  exact (Submodule.Quotient.mk_eq_zero _).1 (Y.m_Q _ hmem)

/-- The map on `P`: `p ↦ ½ h(2p, 0)`. -/
noncomputable def fP : X.P →ₗ[k] Y.P :=
  (half Y.regP).toLinearMap ∘ₗ
    LinearMap.codRestrict (two k Y.P) (aP h) (fun p => (image_ιP h p).2)

/-- The map on `Q`: `q ↦ ½ h(0, 2q)`. -/
noncomputable def fQ : X.Q →ₗ[k] Y.Q :=
  (half Y.regQ).toLinearMap ∘ₗ
    LinearMap.codRestrict (two k Y.Q) (aQ h) (fun q => (image_ιQ h q).2)

lemma two_smul_fP (p : X.P) : 2 • fP h p = aP h p :=
  two_smul_half Y.regP _

lemma two_smul_fQ (q : X.Q) : 2 • fQ h q = aQ h q :=
  two_smul_half Y.regQ _

/-- A `σ`-map out of `N` is determined by what it does on `2P × 2Q`:
`h(p, q) = (f p, g q)`. Since `2N ⊂ 2P × 2Q` and the target is `2`-regular,
no finiteness is needed. -/
lemma apply_eq (z : X.N) :
    ((hh h z : Y.N) : Y.P × Y.Q) =
      (fP h (z : X.P × X.Q).1, fQ h (z : X.P × X.Q).2) := by
  have hz : 2 • z = ιP X (z : X.P × X.Q).1 + ιQ X (z : X.P × X.Q).2 :=
    Subtype.ext (Prod.ext (by simp) (by simp))
  have e : 2 • ((hh h z : Y.N) : Y.P × Y.Q) =
      ((hh h (ιP X (z : X.P × X.Q).1) : Y.N) : Y.P × Y.Q) +
        ((hh h (ιQ X (z : X.P × X.Q).2) : Y.N) : Y.P × Y.Q) := by
    rw [← Submodule.coe_add, ← map_add, ← hz, map_nsmul]
    rfl
  apply Prod.ext
  · apply Y.regP.cancel
    have := congrArg Prod.fst e
    simp only [Prod.smul_fst, Prod.fst_add, (image_ιQ h _).1, add_zero] at this
    rw [this, two_smul_fP, aP_apply]
  · apply Y.regQ.cancel
    have := congrArg Prod.snd e
    simp only [Prod.smul_snd, Prod.snd_add, (image_ιP h _).1, zero_add] at this
    rw [this, two_smul_fQ, aQ_apply]

/-- The preimage of `h` under `build`. -/
noncomputable def preimage : X ⟶ Y where
  f := fP h
  g := fQ h
  hm p q hpq := by
    have h1 := (hh h ⟨(p, q), hpq⟩).2
    rwa [apply_eq] at h1

end Full

instance : (build k).Full where
  map_surjective h := ⟨preimage h, InvMod.hom_ext (LinearMap.ext fun z =>
    Subtype.ext (apply_eq h z).symm)⟩

end Triple

/-! ## The triple of a module with involution, and essential surjectivity -/

namespace InvMod

variable {k}
variable (X : InvMod.{v} k)

/-- The submodule `{(p, q) | p + q ∈ 2M}` of `M₊ × M₋`. -/
def S : Submodule k (X.plus × X.minus) :=
  (two k X.carrier).comap (X.plus.subtype.coprod X.minus.subtype)

/-- The submodule `m ⊂ M₊/2M₊ × M₋/2M₋` of page 90: the image of `2M`. -/
def m : Submodule k ((X.plus ⧸ two k X.plus) × (X.minus ⧸ two k X.minus)) :=
  X.S.map ((two k X.plus).mkQ.prodMap (two k X.minus).mkQ)

/-- `(p̄, q̄) ∈ m` if and only if `p + q ∈ 2M`. -/
theorem mk_mem_m_iff (p : X.plus) (q : X.minus) :
    (Submodule.Quotient.mk p, Submodule.Quotient.mk q) ∈ X.m ↔
      (p : X.carrier) + q ∈ two k X.carrier := by
  refine ⟨?_, fun h => ⟨(p, q), h, rfl⟩⟩
  rintro ⟨⟨p', q'⟩, hS, he⟩
  simp only [LinearMap.prodMap_apply, Submodule.mkQ_apply, Prod.mk.injEq,
    Submodule.Quotient.eq] at he
  obtain ⟨hp, hq⟩ := he
  have hS' : (p' : X.carrier) + q' ∈ two k X.carrier := hS
  have lift : ∀ (N : Submodule k X.carrier) (x : N), x ∈ two k N →
      (x : X.carrier) ∈ two k X.carrier := by
    intro N x hx
    obtain ⟨y, hy⟩ := mem_two.1 hx
    exact mem_two.2 ⟨y, by rw [← hy]; rfl⟩
  have h1 := lift _ _ hp
  have h2 := lift _ _ hq
  simp only [Submodule.coe_sub] at h1 h2
  rw [show (p : X.carrier) + q = ((p' : X.carrier) + q') - (p' - p) - (q' - q) by abel]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hS' h1) h2

/-- The triple `(M₊, M₋, m)` of page 90. -/
def triple : Triple.{v} k where
  P := X.plus
  Q := X.minus
  regP := X.reg.submodule _
  regQ := X.reg.submodule _
  m := X.m
  m_P p hp := by
    induction p using Submodule.Quotient.induction_on with | _ p => ?_
    rw [← Submodule.Quotient.mk_zero (p := two k X.minus), mk_mem_m_iff] at hp
    simp only [Submodule.coe_zero, add_zero] at hp
    exact (Submodule.Quotient.mk_eq_zero _).2 (X.mem_two_of_plus p hp)
  m_Q q hq := by
    induction q using Submodule.Quotient.induction_on with | _ q => ?_
    rw [← Submodule.Quotient.mk_zero (p := two k X.plus), mk_mem_m_iff] at hq
    simp only [Submodule.coe_zero, zero_add] at hq
    exact (Submodule.Quotient.mk_eq_zero _).2 (X.mem_two_of_minus q hq)

/-- The preimage of `m` in `M₊ × M₋` (the module that `build` makes of `triple`). -/
def Nx : Submodule k (X.plus × X.minus) :=
  X.m.comap ((two k X.plus).mkQ.prodMap (two k X.minus).mkQ)

/-- `x ↦ (x + σx, x - σx)`, from `M` into the module rebuilt from its triple. -/
def toBuild : X.carrier →ₗ[k] X.Nx :=
  LinearMap.codRestrict X.Nx
    (LinearMap.prod
      (LinearMap.codRestrict X.plus (LinearMap.id + X.σ) (fun x => X.add_σ_mem_plus x))
      (LinearMap.codRestrict X.minus (LinearMap.id - X.σ) (fun x => X.sub_σ_mem_minus x)))
    (fun x => by
      change (Submodule.Quotient.mk (⟨x + X.σ x, X.add_σ_mem_plus x⟩ : X.plus),
        Submodule.Quotient.mk (⟨x - X.σ x, X.sub_σ_mem_minus x⟩ : X.minus)) ∈ X.m
      rw [mk_mem_m_iff]
      change (x + X.σ x) + (x - X.σ x) ∈ two k X.carrier
      rw [show (x + X.σ x) + (x - X.σ x) = 2 • x by rw [two_nsmul]; abel]
      exact two_smul_mem_two x)

/-- `toBuild` as a morphism `(M, σ) → build (M₊, M₋, m)`. -/
def toBuildHom : X ⟶ (build k).obj X.triple where
  f := X.toBuild
  comm x := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · change X.σ x + X.σ (X.σ x) = x + X.σ x
      rw [X.σ_σ, add_comm]
    · change X.σ x - X.σ (X.σ x) = -(x - X.σ x)
      rw [X.σ_σ, neg_sub]

lemma toBuild_bijective : Function.Bijective X.toBuild := by
  constructor
  · intro x y hxy
    have h1 := congrArg (fun w : X.Nx => ((w : X.plus × X.minus).1 : X.carrier)) hxy
    have h2 := congrArg (fun w : X.Nx => ((w : X.plus × X.minus).2 : X.carrier)) hxy
    change x + X.σ x = y + X.σ y at h1
    change x - X.σ x = y - X.σ y at h2
    apply X.reg.cancel
    rw [two_nsmul, two_nsmul]
    calc x + x = (x + X.σ x) + (x - X.σ x) := by abel
      _ = (y + X.σ y) + (y - X.σ y) := by rw [h1, h2]
      _ = y + y := by abel
  · rintro ⟨⟨p, q⟩, hz⟩
    have hz' : (p : X.carrier) + q ∈ two k X.carrier := (X.mk_mem_m_iff p q).1 hz
    obtain ⟨x, hx⟩ := mem_two.1 hz'
    have hp := (X.mem_plus).1 p.2
    have hq := (X.mem_minus).1 q.2
    have hσx : 2 • X.σ x = (p : X.carrier) - q := by
      rw [← map_nsmul, hx, map_add, hp, hq, sub_eq_add_neg]
    refine ⟨x, Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))⟩
    · change x + X.σ x = p
      apply X.reg.cancel
      rw [smul_add, hx, hσx, two_nsmul]; abel
    · change x - X.σ x = q
      apply X.reg.cancel
      rw [smul_sub, hx, hσx, two_nsmul]; abel

/-- Page 90: `(M, σ)` is rebuilt from `(M₊, M₋, m)`, by `x ↦ (x + σx, x - σx)`
(which is « la multiplication par `2` », `M ≅ M' = 2M ⊂ M₊ ⊕ M₋`). -/
noncomputable def essSurj_witness : (build k).obj X.triple ≅ X :=
  (isoOfBijective X.toBuildHom X.toBuild_bijective).symm

end InvMod

instance : (build k).EssSurj where
  mem_essImage X := ⟨X.triple, ⟨X.essSurj_witness⟩⟩

instance : (build k).IsEquivalence where

/-- **Proposition (page 90).** Two-regular `k`-modules with an involution are
equivalent to triples `(P, Q, m)`. -/
noncomputable def equivalence : Triple.{v} k ≌ InvMod.{v} k :=
  (build k).asEquivalence

/-- The inverse of the equivalence is the page's functor `(M, σ) ↦ (P, Q, m)`:
it sends `(M, σ)` to a triple isomorphic to `(M₊, M₋, m)`. -/
noncomputable def inverse_obj_iso (X : InvMod.{v} k) :
    (equivalence k).inverse.obj X ≅ X.triple :=
  (build k).preimageIso ((equivalence k).counitIso.app X ≪≫ X.essSurj_witness.symm)

end Grothendieck.Folder67
