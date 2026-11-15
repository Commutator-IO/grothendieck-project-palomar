module

public import Mathlib
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Powerset

@[expose] public section


/-!
# Folder 156-5: the set-theoretic model of the axioms, and the gluing of ultra-topologies

The modernised reading `transcripts/156-5/156-5.modern.tex` reads chapter V of *Vers une
géométrie des formes*, « Algèbre des figures » (14–18 June 1986), written between the first
mouture of the Analysis situs (folder 156-4) and the second (156-6). A *figure* of a set `L` is
an admissible family of parts of `L`: every point of its support has a least member containing
it, and every member `A` has a non-empty open stratum `A° = A ∖ ⋃ {B ∈ F | B ⊊ A}`. Page 36
(18 June) observes that a figure is the same thing as a part `S ⊂ L` with an
« ultra-topologie » — an Alexandrov topology, that is a preorder, the members being the
closures of the points.

Proved here, in three parts.

* **Pages 12–14, the components of `𝓜`.** `Mult`: the multiplicities (figures with a greatest
  member); `SameComp`: the connected components of `(𝓜, ≤)`, `≤` being « sous-figure ».
  `sameComp_univ`: the multiplicity `{L}` is alone in its component. `not_compatible_univ`:
  `{L}` and `{{x}}` are incompatible as soon as `L ≠ {x}`. `not_C4`: for any `L` with two
  distinct points, the axiom C 4 of the first mouture (two multiplicities in different
  components are compatible) fails, and `𝓜` is not connected — against the « Prop. » of
  page 13, which asserts connectedness and the vacuity of C 4, for finite figures in
  particular.
* **Pages 38–40, 45 and 48, the glued topology.** Ultra-topologies are encoded by their
  specialisation preorders `x ≤ y ⇔ x ∈ closure {y}`; closed sets are down-closed sets
  (`DownClosed`), and a finer topology has a smaller preorder. For `T` closed in `(S, τ)` and
  `τ'₀` finer than `τ` on `T`, `glue` is the preorder of point (d) of the lemma of
  pages 40–41. `glue_isPreorder`, `glue_admits`: it is a preorder, finer than `τ`, inducing
  `τ'₀`. `le_glue`: every such topology `τ''` is finer than it, so `τ'` is the least fine one
  (point (a)). `glue_downClosed_iff`: the corollary of page 45, `τ` is final for
  `(S, τ') → S` and `(T, τ|_T) → S`. `eq_glue_iff`, `eq_glue_iff_closure`: the closing
  condition of page 48 — among the topologies of `𝔗`, `τ'` is the one in which every part
  of `U = S ∖ T` has the same closure as for `τ`.
* **Page 48, « C'est ultra faux ».** `ThreePoint`: the edition's explicit form of the drawn
  counter-example, `S = {a, b, c}`, `T = {a, c}`, `τ` with `a ∼ c < b`, `τ'₀` discrete, and the
  competitor `τ''` with `a < b` only. `threePoint_e_false`: `τ''` satisfies (i)–(iv) of the
  characterisation e) of pages 41–42 and differs from `τ'`.

**What the formalisation finds.** The gluing lemma and the closing characterisation of
page 48 hold for arbitrary preorders, without finiteness; the three-point model refutes e)
exactly as page 48 says. The connectedness of `𝓜` asserted on pages 12–14 is false for every
`L` with at least two points, already with finite figures, and with it the claimed vacuity
of C 4: the multiplicity `{L}` has no sub-figure but itself and `∅`, and no figure containing
it as a sub-figure but itself. The figures themselves are encoded only in the first part;
the second and third parts work directly with preorders, which page 36 identifies with
figures.
-/

namespace Grothendieck.Folder156_5

/-! ## Part 1. Figures, multiplicities, and the axiom C 4 (pages 3, 6, 11–14) -/

section Figures

variable {L : Type*}

/-- The open stratum `A° = A ∖ ⋃ {B ∈ F | B ⊊ A}` of a member `A` of the family `F`. -/
def stratum (F : Set (Set L)) (A : Set L) : Set L :=
  A \ ⋃₀ {B | B ∈ F ∧ B ⊂ A}

/-- An admissible family (page 3): every point of a member lies in a least member, and every
member has a non-empty open stratum. -/
def Admissible (F : Set (Set L)) : Prop :=
  (∀ x, ∀ A ∈ F, x ∈ A → ∃ A₀ ∈ F, x ∈ A₀ ∧ ∀ B ∈ F, x ∈ B → A₀ ⊆ B) ∧
    ∀ A ∈ F, (stratum F A).Nonempty

/-- `G` is a sub-figure of `F` (pages 6–7): a part of `F` stable under passing to smaller
members. -/
def SubFig (G F : Set (Set L)) : Prop :=
  G ⊆ F ∧ ∀ A ∈ G, ∀ B ∈ F, B ⊆ A → B ∈ G

/-- A multiplicity (page 11): a figure with a greatest member. -/
def Mult (F : Set (Set L)) : Prop :=
  Admissible F ∧ ∃ A ∈ F, ∀ B ∈ F, B ⊆ A

/-- Two figures are compatible (page 7, a')) when they are sub-figures of a same figure. -/
def Compatible (F G : Set (Set L)) : Prop :=
  ∃ H, Admissible H ∧ SubFig F H ∧ SubFig G H

/-- Comparability in the ordered set `(𝓜, ≤)`. -/
def Adj (F G : Set (Set L)) : Prop :=
  Mult F ∧ Mult G ∧ (SubFig F G ∨ SubFig G F)

/-- Two multiplicities are in the same connected component of `(𝓜, ≤)`. -/
def SameComp (F G : Set (Set L)) : Prop :=
  Relation.EqvGen Adj F G

theorem subFig_univ {G : Set (Set L)} (h : SubFig {Set.univ} G) : G = {Set.univ} := by
  have hu : Set.univ ∈ G := h.1 rfl
  ext B
  constructor
  · intro hB
    exact h.2 _ rfl B hB (Set.subset_univ B)
  · rintro rfl
    exact hu

theorem eq_univ_of_subFig {G : Set (Set L)} (hG : Mult G) (h : SubFig G {Set.univ}) :
    G = {Set.univ} := by
  obtain ⟨_, A, hA, -⟩ := hG
  have hA' : A = Set.univ := h.1 hA
  subst hA'
  exact Set.Subset.antisymm h.1 (Set.singleton_subset_iff.2 hA)

theorem mult_univ [Nonempty L] : Mult ({Set.univ} : Set (Set L)) := by
  refine ⟨⟨?_, ?_⟩, Set.univ, rfl, fun B hB => hB ▸ subset_rfl⟩
  · rintro x A rfl -
    exact ⟨Set.univ, rfl, Set.mem_univ x, fun B hB _ => hB ▸ subset_rfl⟩
  · rintro A rfl
    obtain ⟨x⟩ := ‹Nonempty L›
    refine ⟨x, Set.mem_univ x, ?_⟩
    rintro ⟨B, ⟨hB, hBs⟩, -⟩
    rw [Set.mem_singleton_iff] at hB
    exact hBs.ne hB

theorem mult_singleton (x : L) : Mult ({{x}} : Set (Set L)) := by
  refine ⟨⟨?_, ?_⟩, {x}, rfl, fun B hB => hB ▸ subset_rfl⟩
  · rintro y A rfl hy
    exact ⟨{x}, rfl, hy, fun B hB _ => hB ▸ subset_rfl⟩
  · rintro A rfl
    refine ⟨x, rfl, ?_⟩
    rintro ⟨B, ⟨hB, hBs⟩, -⟩
    rw [Set.mem_singleton_iff] at hB
    exact hBs.ne hB

/-- Pages 12–14: the multiplicity `{L}` is alone in its connected component of `(𝓜, ≤)`. -/
theorem sameComp_univ {G : Set (Set L)} (h : SameComp {Set.univ} G) : G = {Set.univ} := by
  suffices key : ∀ F G : Set (Set L), SameComp F G → (F = {Set.univ} ↔ G = {Set.univ}) from
    (key _ _ h).1 rfl
  intro F G hFG
  induction hFG with
  | rel F G hadj =>
    obtain ⟨hF, hG, hsub | hsub⟩ := hadj
    · constructor
      · rintro rfl; exact subFig_univ hsub
      · rintro rfl; exact eq_univ_of_subFig hF hsub
    · constructor
      · rintro rfl; exact eq_univ_of_subFig hG hsub
      · rintro rfl; exact subFig_univ hsub
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `{L}` and `{{x}}` are not compatible when `L ≠ {x}`. -/
theorem not_compatible_univ {x : L} (hx : (Set.univ : Set L) ≠ {x}) :
    ¬ Compatible {Set.univ} {{x}} := by
  rintro ⟨H, -, hH, hH'⟩
  have h1 := subFig_univ hH
  have h2 : ({x} : Set L) ∈ H := hH'.1 rfl
  rw [h1, Set.mem_singleton_iff] at h2
  exact hx h2.symm

/-- Pages 12–14: as soon as `L` has two distinct points, `{L}` and `{{x}}` are multiplicities
in different components of `𝓜` which are not compatible. So `𝓜` is not connected and the
axiom C 4 fails. -/
theorem not_C4 {x y : L} (hxy : x ≠ y) :
    Mult ({Set.univ} : Set (Set L)) ∧ Mult ({{x}} : Set (Set L)) ∧
      ¬ SameComp ({Set.univ} : Set (Set L)) {{x}} ∧
      ¬ Compatible ({Set.univ} : Set (Set L)) {{x}} ∧
      ¬ (∀ F G : Set (Set L), Mult F → Mult G → ¬ SameComp F G → Compatible F G) := by
  have : Nonempty L := ⟨x⟩
  have hx : (Set.univ : Set L) ≠ {x} := by
    intro h
    have : y ∈ ({x} : Set L) := h ▸ Set.mem_univ y
    exact hxy (Set.mem_singleton_iff.1 this).symm
  have hne : ¬ SameComp ({Set.univ} : Set (Set L)) {{x}} := by
    intro h
    have h' := sameComp_univ h
    have : ({x} : Set L) ∈ ({Set.univ} : Set (Set L)) := h' ▸ rfl
    exact hx (Set.mem_singleton_iff.1 this).symm
  refine ⟨mult_univ, mult_singleton x, hne, not_compatible_univ hx, ?_⟩
  intro hC4
  exact not_compatible_univ hx (hC4 _ _ mult_univ (mult_singleton x) hne)

end Figures

/-! ## Part 2. The glued ultra-topology (pages 38–48)

An ultra-topology is encoded by its specialisation preorder `p x y ⇔ x ∈ closure {y}`; the
closed sets are the down-closed sets, a topology is finer when its preorder is smaller. -/

section Glue

variable {α : Type*}

/-- `p` is a preorder relation. -/
def IsPre (p : α → α → Prop) : Prop :=
  (∀ x, p x x) ∧ ∀ x y z, p x y → p y z → p x z

/-- `X` is closed for the ultra-topology of `p`. -/
def DownClosed (p : α → α → Prop) (X : Set α) : Prop :=
  ∀ x y, p x y → y ∈ X → x ∈ X

/-- The closure of `A` for the ultra-topology of `p`. -/
def cl (p : α → α → Prop) (A : Set α) : Set α :=
  {x | ∃ a ∈ A, p x a}

/-- The preorder of the glued topology `τ'` (point (d) of the lemma of pages 40–41): on `T`
the preorder of `τ'₀`; below a point of `U = S ∖ T`, the preorder of `τ`; never a point of `U`
below a point of `T`. -/
def glue (r : α → α → Prop) (T : Set α) (r₀ : α → α → Prop) (x y : α) : Prop :=
  (x ∈ T ∧ y ∈ T ∧ r₀ x y) ∨ (y ∉ T ∧ r x y)

/-- The set `𝔗` of the lemma of page 40: topologies finer than `τ` inducing `τ'₀` on `T`. -/
def Admits (r : α → α → Prop) (T : Set α) (r₀ : α → α → Prop) (h : α → α → Prop) : Prop :=
  (∀ x y, h x y → r x y) ∧ ∀ x ∈ T, ∀ y ∈ T, (h x y ↔ r₀ x y)

variable {r r₀ : α → α → Prop} {T : Set α}

theorem glue_isPreorder (hr : IsPre r) (hr₀ : IsPre r₀) (h₀ : ∀ x ∈ T, ∀ y ∈ T, r₀ x y → r x y) :
    IsPre (glue r T r₀) := by
  refine ⟨fun x => ?_, fun x y z hxy hyz => ?_⟩
  · by_cases hx : x ∈ T
    · exact Or.inl ⟨hx, hx, hr₀.1 x⟩
    · exact Or.inr ⟨hx, hr.1 x⟩
  · rcases hyz with ⟨hy, hz, hyz⟩ | ⟨hz, hyz⟩
    · rcases hxy with ⟨hx, -, hxy⟩ | ⟨hy', -⟩
      · exact Or.inl ⟨hx, hz, hr₀.2 _ _ _ hxy hyz⟩
      · exact absurd hy hy'
    · have hxy' : r x y := by
        rcases hxy with ⟨hx, hy, hxy⟩ | ⟨-, hxy⟩
        · exact h₀ x hx y hy hxy
        · exact hxy
      exact Or.inr ⟨hz, hr.2 _ _ _ hxy' hyz⟩

/-- The glued topology belongs to `𝔗`. -/
theorem glue_admits (h₀ : ∀ x ∈ T, ∀ y ∈ T, r₀ x y → r x y) : Admits r T r₀ (glue r T r₀) := by
  refine ⟨fun x y hxy => ?_, fun x hx y hy => ⟨fun hxy => ?_, fun hxy => Or.inl ⟨hx, hy, hxy⟩⟩⟩
  · rcases hxy with ⟨hx, hy, hxy⟩ | ⟨-, hxy⟩
    · exact h₀ x hx y hy hxy
    · exact hxy
  · rcases hxy with ⟨-, -, hxy⟩ | ⟨hy', -⟩
    · exact hxy
    · exact absurd hy hy'

/-- Lemma of page 40, point (a): every topology of `𝔗` is finer than `τ'`, which is therefore
the least fine element of `𝔗`. -/
theorem le_glue (hT : DownClosed r T) {h : α → α → Prop} (hh : Admits r T r₀ h) {x y : α}
    (hxy : h x y) : glue r T r₀ x y := by
  by_cases hy : y ∈ T
  · have hx : x ∈ T := hT x y (hh.1 x y hxy) hy
    exact Or.inl ⟨hx, hy, (hh.2 x hx y hy).1 hxy⟩
  · exact Or.inr ⟨hy, hh.1 x y hxy⟩

/-- For `τ'`, the closure of a point of `U` is its closure for `τ`. -/
theorem glue_of_not_mem {y : α} (hy : y ∉ T) (x : α) : glue r T r₀ x y ↔ r x y := by
  constructor
  · rintro (⟨-, hy', -⟩ | ⟨-, hxy⟩)
    · exact absurd hy' hy
    · exact hxy
  · exact fun hxy => Or.inr ⟨hy, hxy⟩

/-- Corollary of page 45 (property (iv) of page 42, on `S`): a part of `S` is closed for `τ` iff
it is closed for `τ'` and its trace on `T` is closed for `τ|_T`. -/
theorem glue_downClosed_iff (hT : DownClosed r T) (h₀ : ∀ x ∈ T, ∀ y ∈ T, r₀ x y → r x y)
    (X : Set α) :
    DownClosed r X ↔
      DownClosed (glue r T r₀) X ∧ ∀ x y, x ∈ T → y ∈ T → r x y → y ∈ X → x ∈ X := by
  constructor
  · intro hX
    exact ⟨fun x y hxy hy => hX x y ((glue_admits h₀).1 x y hxy) hy,
      fun x y _ _ hxy hy => hX x y hxy hy⟩
  · rintro ⟨hX, hXT⟩ x y hxy hy
    by_cases hyT : y ∈ T
    · exact hXT x y (hT x y hxy hyT) hyT hxy hy
    · exact hX x y (Or.inr ⟨hyT, hxy⟩) hy

/-- Page 48, the closing condition, for points: a topology of `𝔗` is `τ'` iff every point of
`U` has the same closure as for `τ`. -/
theorem eq_glue_iff (hT : DownClosed r T) {h : α → α → Prop} (hh : Admits r T r₀ h) :
    (∀ y, y ∉ T → ∀ x, (h x y ↔ r x y)) ↔ ∀ x y, (h x y ↔ glue r T r₀ x y) := by
  constructor
  · intro hU x y
    refine ⟨le_glue hT hh, ?_⟩
    rintro (⟨hx, hy, hxy⟩ | ⟨hy, hxy⟩)
    · exact (hh.2 x hx y hy).2 hxy
    · exact (hU y hy x).2 hxy
  · intro he y hy x
    exact (he x y).trans (glue_of_not_mem hy x)

/-- Page 48, the closing condition as written: « pour `A ⊂ U`, l'adhérence de `A` pour `τ` et
pour `τ'` est la même » characterises `τ'` in `𝔗`. -/
theorem eq_glue_iff_closure (hT : DownClosed r T) {h : α → α → Prop} (hh : Admits r T r₀ h) :
    (∀ A : Set α, A ⊆ Tᶜ → cl h A = cl r A) ↔ ∀ x y, (h x y ↔ glue r T r₀ x y) := by
  rw [← eq_glue_iff hT hh]
  constructor
  · intro hA y hy x
    have := congrArg (x ∈ ·) (hA {y} (Set.singleton_subset_iff.2 hy))
    simpa [cl] using this
  · intro hU A hA
    ext x
    simp only [cl, Set.mem_ofPred_eq]
    exact exists_congr fun a => and_congr_right fun ha => hU a (hA ha) x

end Glue

/-! ## Part 3. The three-point counter-example of page 48

`a = 0`, `b = 1`, `c = 2`; `T = {a, c}`, `U = {b}`. -/

namespace ThreePoint

/-- `τ`: `a` and `c` equivalent, both below `b`. -/
def r (x y : Fin 3) : Prop := y = 1 ∨ x ≠ 1

/-- `τ'₀`: the discrete order on `T`. -/
def r₀ (x y : Fin 3) : Prop := x = y

/-- The closed part `T = {a, c}`. -/
def T : Set (Fin 3) := {x | x ≠ 1}

/-- The competitor `τ''`: `a < b`, `c` isolated. -/
def h (x y : Fin 3) : Prop := x = y ∨ (x = 0 ∧ y = 1)

instance : DecidableRel r := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel h := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred (· ∈ T) := fun _ => inferInstanceAs (Decidable (_ ≠ _))

end ThreePoint

set_option synthInstance.maxSize 1024 in
open ThreePoint in
/-- Page 48, « C'est ultra faux » : in the three-point model, `τ''` satisfies (i) finer than `τ`
and inducing `τ'₀` on `T`, (iii) inducing `τ` on `U`, (iv) `τ` final for `(S, τ'') → S` and
`(T, τ|_T) → S`, and still differs from `τ'`: the closure of `{b}` is `S` for `τ` and `τ'`,
`{a, b}` for `τ''`. The data satisfy the hypotheses of the lemma of page 40. -/
theorem threePoint_e_false :
    IsPre r ∧ IsPre r₀ ∧ DownClosed r T ∧ (∀ x ∈ T, ∀ y ∈ T, r₀ x y → r x y) ∧
      IsPre h ∧ Admits r T r₀ h ∧
      (∀ x ∉ T, ∀ y ∉ T, (h x y ↔ r x y)) ∧
      (∀ X : Finset (Fin 3), DownClosed r (X : Set (Fin 3)) ↔
        DownClosed h (X : Set (Fin 3)) ∧
          ∀ x y, x ∈ T → y ∈ T → r x y → y ∈ (X : Set (Fin 3)) → x ∈ (X : Set (Fin 3))) ∧
      ¬ h 2 1 ∧ glue r T r₀ 2 1 ∧ r 2 1 := by
  simp only [IsPre, DownClosed, Admits, glue, T, r, r₀, h, Set.mem_ofPred_eq, Finset.mem_coe]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Grothendieck.Folder156_5
