module

public import Mathlib

@[expose] public section


/-!
# Folder 154, page 153: the cube of generisations

Finding `154-generisation-cube` (`src/content/findings.ts`), on the reading
`transcripts/154/154.modern.tex` (« Le cube des générisations »). Page 153: for a position `D`
of an added pseudoline passing through `ν ≥ 2` vertices of the arrangement `Σ`, « les
générisations stables de `D` correspondent aux sommets d'un cube de dimension `ν`, dont les
arêtes sont les générisations sous-stables », with the counts `2^ν` and `ν 2^(ν−1)`.

**The model** (the edition's precise statement, mathlib having no oriented matroids). A position
of an added pseudoline is a single-element extension of the rank-3 oriented matroid of `Σ`,
given by Las Vergnas's signature on the cocircuits (the vertices); since `σ(−Y) = −σ(Y)`, it is
a map `σ : V → SignType` on one chosen representative of each vertex. A line `ℓ` of `Σ` is the
sequence of the vertices it carries, read along its double cover from a base point, each with a
sign `ori ℓ i = ±1` comparing the chosen representative with the orientation of `ℓ`
(`Arrangement`). Las Vergnas's criterion, checked line by line (`ValidSeq`, `IsPosition`): along
each line the signs `ori ℓ i · σ(vᵢ)` read `+ … + (0) − … −` up to reversal, at most one `0`,
not all zero. `σ` is a specialisation of `τ` (`Spec σ τ`) when `τ = σ` wherever `σ ≠ 0`.

* `ValidSeq.eq_of_eq_zero`, `IsPosition.eq_of_zero_on_line`: a line carries at most one zero of
  a position — two vertices of `D` never lie on a common line of `Σ`;
* `ValidSeq.of_agree`, `IsPosition.of_spec`: every sign vector more generic than a position is a
  position — the « unsticking » at each vertex of `D` is a free choice of sign, independently;
* `genEquiv`, `genEquiv_spec_iff`: the positions `σ ≥ σ_D` are in bijection with all the sign
  vectors on the `ν` zeros of `σ_D`, specialisation corresponding to specialisation;
* `cubeFace_subset_iff`, `cubeFace_eq_singleton`: those sign vectors, ordered by
  specialisation, are the faces of the cube `[−1, 1]^ν` ordered by reverse inclusion, the
  vectors without zero being its vertices;
* `card_gen`, `card_gen_stable`, `card_gen_substable`: there are `3^ν` generisations of `D`,
  `2^ν` stable ones (no zero) and `ν · 2^(ν−1)` sub-stable ones (exactly one zero).

The hypothesis `ν ≥ 2` is not needed, nor the axioms of an arrangement (two lines meet in one
vertex, …): the statement holds for any such data. Not formalised: positions as topological
pseudolines (that would need the topological representation theorem of Folkman–Lawrence), the
surface `X*` of page 150 and the tension with it for `ν ≥ 3`, and the question of page 153.
-/

namespace Grothendieck.Folder154

/-! ## Las Vergnas's condition on one line -/

/-- The signs read along a line are valid: not all zero, and of the form `a … a (x) −a … −a`
with `a = ±1`, the middle `x` (at position `c`) being `a`, `0` or `−a`: that is
`+ … + (0) − … −` up to reversal, with at most one zero. -/
def ValidSeq {n : ℕ} (s : Fin n → SignType) : Prop :=
  (∃ i, s i ≠ 0) ∧ ∃ a : SignType, a ≠ 0 ∧ ∃ c : ℕ,
    (∀ i : Fin n, (i : ℕ) < c → s i = a) ∧ (∀ i : Fin n, c < (i : ℕ) → s i = -a)

lemma neg_ne_zero' {a : SignType} (ha : a ≠ 0) : -a ≠ 0 := by
  simpa

/-- A valid sequence has at most one zero. -/
theorem ValidSeq.eq_of_eq_zero {n : ℕ} {s : Fin n → SignType} (h : ValidSeq s) {i j : Fin n}
    (hi : s i = 0) (hj : s j = 0) : i = j := by
  obtain ⟨-, a, ha, c, h1, h2⟩ := h
  have key : ∀ k : Fin n, s k = 0 → (k : ℕ) = c := fun k hk => by
    rcases lt_trichotomy (k : ℕ) c with h | h | h
    · exact absurd ((h1 k h).symm.trans hk) ha
    · exact h
    · exact absurd ((h2 k h).symm.trans hk) (neg_ne_zero' ha)
  exact Fin.ext ((key i hi).trans (key j hj).symm)

/-- A sequence agreeing with a valid one wherever the latter is nonzero is valid. -/
theorem ValidSeq.of_agree {n : ℕ} {s t : Fin n → SignType} (h : ValidSeq s)
    (hst : ∀ i, s i ≠ 0 → t i = s i) : ValidSeq t := by
  obtain ⟨⟨j, hj⟩, a, ha, c, h1, h2⟩ := h
  exact ⟨⟨j, by rwa [hst j hj]⟩, a, ha, c, fun i hi => by rw [hst i (by rwa [h1 i hi]), h1 i hi],
    fun i hi => by rw [hst i (by rw [h2 i hi]; exact neg_ne_zero' ha), h2 i hi]⟩

/-! ## Arrangements and positions -/

/-- The combinatorial data of an arrangement `Σ`: vertices `V` (one representative cocircuit
for each antipodal pair), lines `L`; line `ℓ` carries the vertices `vert ℓ 0, …` in the order
of its double cover from a base point, `ori ℓ i = ±1` comparing the representative of
`vert ℓ i` with the orientation of `ℓ`. -/
structure Arrangement (V : Type*) (L : Type*) where
  /-- The number of vertices on a line. -/
  len : L → ℕ
  /-- The vertices of a line, in order. -/
  vert : (ℓ : L) → Fin (len ℓ) → V
  vert_injective : ∀ ℓ, Function.Injective (vert ℓ)
  /-- The sign correcting the chosen representative of each vertex along the line. -/
  ori : (ℓ : L) → Fin (len ℓ) → SignType
  ori_ne_zero : ∀ ℓ i, ori ℓ i ≠ 0

/-- `σ` is a specialisation of `τ` (`τ` a generisation of `σ`): `τ = σ` wherever `σ ≠ 0`. -/
def Spec {X : Type*} (σ τ : X → SignType) : Prop := ∀ x, σ x ≠ 0 → τ x = σ x

namespace Arrangement

variable {V L : Type*} (A : Arrangement V L)

/-- The signs of a signature read along the line `ℓ`. -/
def restr (σ : V → SignType) (ℓ : L) : Fin (A.len ℓ) → SignType :=
  fun i => A.ori ℓ i * σ (A.vert ℓ i)

/-- A position of an added pseudoline: a cocircuit signature valid on every line of `Σ`
(Las Vergnas's criterion, with the edition's exclusion of the lines of `Σ` themselves). -/
def IsPosition (σ : V → SignType) : Prop := ∀ ℓ, ValidSeq (A.restr σ ℓ)

variable {A}

/-- Two zeros of a position never lie on a common line of `Σ`. -/
theorem IsPosition.eq_of_zero_on_line {σ : V → SignType} (h : A.IsPosition σ) (ℓ : L)
    {i j : Fin (A.len ℓ)} (hi : σ (A.vert ℓ i) = 0) (hj : σ (A.vert ℓ j) = 0) : i = j :=
  (h ℓ).eq_of_eq_zero (by simp [restr, hi]) (by simp [restr, hj])

/-- Independence of the choices: every generisation, as a sign vector, of a position is a
position. -/
theorem IsPosition.of_spec {σ τ : V → SignType} (h : A.IsPosition σ) (hst : Spec σ τ) :
    A.IsPosition τ := fun ℓ =>
  (h ℓ).of_agree fun i hi => by
    simp only [restr] at hi ⊢
    rw [hst _ (right_ne_zero_of_mul hi)]

/-- The positions `σ ≥ σ_D` are exactly the sign vectors `σ ≥ σ_D`. -/
theorem isPosition_and_spec_iff {σD σ : V → SignType} (hD : A.IsPosition σD) :
    A.IsPosition σ ∧ Spec σD σ ↔ Spec σD σ :=
  ⟨And.right, fun h => ⟨hD.of_spec h, h⟩⟩

/-- The generisations of the position `σ_D`. -/
abbrev Gen (A : Arrangement V L) (σD : V → SignType) :=
  {σ : V → SignType // A.IsPosition σ ∧ Spec σD σ}

/-- The generisations of `σ_D` are the sign vectors on the zeros of `σ_D`: restriction. -/
def genEquiv {σD : V → SignType} (hD : A.IsPosition σD) :
    A.Gen σD ≃ ({v // σD v = 0} → SignType) where
  toFun σ z := σ.1 z.1
  invFun w := ⟨fun v => if h : σD v = 0 then w ⟨v, h⟩ else σD v,
    (isPosition_and_spec_iff hD).2 fun v hv => by simp [hv]⟩
  left_inv σ := by
    refine Subtype.ext (funext fun v => ?_)
    by_cases h : σD v = 0 <;> simp [h, σ.2.2 v]
  right_inv w := funext fun z => by simp [z.2]

/-- Specialisation among the generisations of `σ_D` is specialisation of the sign vectors on
the zeros of `σ_D`. -/
theorem genEquiv_spec_iff {σD : V → SignType} (hD : A.IsPosition σD) (σ τ : A.Gen σD) :
    Spec σ.1 τ.1 ↔ Spec (genEquiv hD σ) (genEquiv hD τ) := by
  refine ⟨fun h z hz => h z.1 hz, fun h v hv => ?_⟩
  by_cases hz : σD v = 0
  · exact h ⟨v, hz⟩ hv
  · rw [τ.2.2 v hz, σ.2.2 v hz]

end Arrangement

/-! ## The cube -/

section Cube

variable {X : Type*}

/-- The face of the cube `[−1, 1]^X` with sign vector `w`: coordinate `z` is fixed to `w z`
where `w z ≠ 0`, free where `w z = 0`. -/
def cubeFace (w : X → SignType) : Set (X → ℝ) :=
  {x | (∀ z, |x z| ≤ 1) ∧ ∀ z, w z ≠ 0 → x z = (w z : ℝ)}

lemma cast_injective : Function.Injective (fun s : SignType => (s : ℝ)) := by
  intro a b h
  cases a <;> cases b <;> norm_num at h <;> rfl

lemma abs_cast_le_one (s : SignType) : |(s : ℝ)| ≤ 1 := by
  cases s <;> simp

/-- Incidence of faces is specialisation: the face `w` lies in the face `w'` iff `w'` is a
specialisation of `w`. -/
theorem cubeFace_subset_iff (w w' : X → SignType) : cubeFace w ⊆ cubeFace w' ↔ Spec w' w := by
  constructor
  · intro h z hz
    exact cast_injective ((h (a := fun z => (w z : ℝ)) ⟨fun z => abs_cast_le_one _,
      fun _ _ => rfl⟩).2 z hz)
  · rintro h x ⟨hx1, hx2⟩
    exact ⟨hx1, fun z hz => by rw [hx2 z (by rwa [h z hz]), h z hz]⟩

/-- A sign vector without zero is a vertex of the cube. -/
theorem cubeFace_eq_singleton {w : X → SignType} (hw : ∀ z, w z ≠ 0) :
    cubeFace w = {fun z => (w z : ℝ)} := by
  ext x
  simp only [cubeFace, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · exact fun ⟨_, h⟩ => funext fun z => h z (hw z)
  · rintro rfl
    exact ⟨fun z => abs_cast_le_one _, fun _ _ => rfl⟩

/-- The unique zero of a sign vector with exactly one zero. -/
noncomputable def theZero (w : {w : X → SignType // ∃! z, w z = 0}) : X :=
  w.2.exists.choose

lemma theZero_spec (w : {w : X → SignType // ∃! z, w z = 0}) : w.1 (theZero w) = 0 :=
  w.2.exists.choose_spec

lemma eq_theZero (w : {w : X → SignType // ∃! z, w z = 0}) {z : X} (hz : w.1 z = 0) :
    z = theZero w :=
  w.2.unique hz (theZero_spec w)

variable [Fintype X]

/-- `3^ν` faces. -/
theorem card_signVectors : Nat.card (X → SignType) = 3 ^ Fintype.card X := by
  simp [Nat.card_pi, Nat.card_eq_fintype_card]
  rfl

lemma card_ne_zero_signType : Nat.card {s : SignType // s ≠ 0} = 2 := by
  rw [Nat.card_eq_fintype_card]; rfl

/-- `2^ν` vertices: the sign vectors without zero. -/
theorem card_stable : Nat.card {w : X → SignType // ∀ z, w z ≠ 0} = 2 ^ Fintype.card X := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : X => SignType)
    (p := fun _ s => s ≠ 0)), Nat.card_pi]
  simp only [card_ne_zero_signType, Finset.prod_const, Finset.card_univ]

variable [DecidableEq X]

/-- The sign vectors with exactly one zero, at `z`, are the sign vectors without zero on the
other coordinates. -/
noncomputable def fiberEquiv (z : X) :
    {w : {w : X → SignType // ∃! z, w z = 0} // theZero w = z} ≃
      ({y // y ≠ z} → {s : SignType // s ≠ 0}) where
  toFun w y := ⟨w.1.1 y.1, fun h => y.2 ((eq_theZero w.1 h).trans w.2)⟩
  invFun g :=
    have hg : ∃! y, (fun y => if h : y = z then 0 else (g ⟨y, h⟩).1) y = 0 :=
      ⟨z, by simp, fun y hy => by
        by_contra hne
        simp only [hne, dite_false] at hy
        exact (g ⟨y, hne⟩).2 hy⟩
    ⟨⟨_, hg⟩, (eq_theZero ⟨_, hg⟩ (by simp)).symm⟩
  left_inv w := by
    refine Subtype.ext (Subtype.ext (funext fun y => ?_))
    by_cases h : y = z
    · subst h
      simpa [w.2] using (theZero_spec w.1).symm
    · simp [h]
  right_inv g := funext fun y => Subtype.ext (by simp [y.2])

/-- `ν · 2^(ν−1)` edges: the sign vectors with exactly one zero. -/
theorem card_substable :
    Nat.card {w : X → SignType // ∃! z, w z = 0} =
      Fintype.card X * 2 ^ (Fintype.card X - 1) := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv theZero), Nat.card_sigma]
  simp_rw [Nat.card_congr (fiberEquiv _), Nat.card_pi, card_ne_zero_signType]
  simp [Fintype.card_subtype_compl]

end Cube

/-! ## The cube of generisations (page 153) -/

namespace Arrangement

variable {V L : Type*} [Fintype V] {A : Arrangement V L} {σD : V → SignType}

/-- The generisations of `D`: `3^ν`, one for each face of the `ν`-cube, `ν` the number of
vertices through which `D` passes. -/
theorem card_gen (hD : A.IsPosition σD) :
    Nat.card (A.Gen σD) = 3 ^ Fintype.card {v // σD v = 0} := by
  rw [Nat.card_congr (genEquiv hD), card_signVectors]

/-- Page 153: the stable generisations of `D` (no zero) are `2^ν`, the vertices of the cube. -/
theorem card_gen_stable (hD : A.IsPosition σD) :
    Nat.card {σ : A.Gen σD // ∀ v, σ.1 v ≠ 0} = 2 ^ Fintype.card {v // σD v = 0} := by
  rw [← card_stable]
  refine Nat.card_congr ((genEquiv hD).subtypeEquiv fun σ => ⟨fun h z => h z.1, fun h v => ?_⟩)
  by_cases hz : σD v = 0
  · exact h ⟨v, hz⟩
  · rwa [σ.2.2 v hz]

/-- Page 153: the sub-stable generisations of `D` (exactly one zero) are `ν · 2^(ν−1)`, the
edges of the cube. -/
theorem card_gen_substable (hD : A.IsPosition σD) :
    Nat.card {σ : A.Gen σD // ∃! v, σ.1 v = 0} =
      Fintype.card {v // σD v = 0} * 2 ^ (Fintype.card {v // σD v = 0} - 1) := by
  classical
  rw [← card_substable]
  refine Nat.card_congr ((genEquiv hD).subtypeEquiv fun σ => ?_)
  have hzero : ∀ v, σ.1 v = 0 → σD v = 0 := fun v hv => by
    by_contra h
    exact h (σ.2.2 v h ▸ hv)
  constructor
  · rintro ⟨v, hv, hu⟩
    exact ⟨⟨v, hzero v hv⟩, hv, fun z hz => Subtype.ext (hu z.1 hz)⟩
  · rintro ⟨z, hz, hu⟩
    exact ⟨z.1, hz, fun v hv => congrArg Subtype.val (hu ⟨v, hzero v hv⟩ hv)⟩

end Arrangement

/-! ## Problem 17 of `docs/problems/article.tex`: an added pseudoline and its crossing order (statement only)

Page 18 asserts, « il ne devrait pas être difficile de montrer », that the position of an
added pseudoline is determined by the antipody-compatible cyclic order in which its double
cover meets the pseudolines of `Σ`. In oriented-matroid terms (rank 3, Folkman–Lawrence),
the added pseudoline is a single-element extension, and its cyclic crossing order is the
rank-2 contraction at the new element.

The statement is here as a `Prop`, proved (`problem17_holds`) from alternation alone: the triples through the new element are read off the
contraction, the others off `Σ`. What the page asks needs, in addition, the dictionary from
pseudolines to chirotopes (the topological representation theorem) and from the cyclic order
to the contraction, which Mathlib does not have. -/

section Problem17

/-- Rank-3 chirotopes: alternating, not identically zero, and satisfying the three-term
Grassmann–Plücker relations (Björner–Las Vergnas–Sturmfels–White–Ziegler, Def. 3.5.3). -/
structure Chirotope3 (E : Type) where
  χ : E → E → E → SignType
  nonzero : ∃ a b c, χ a b c ≠ 0
  swap12 : ∀ a b c, χ b a c = -χ a b c
  swap23 : ∀ a b c, χ a c b = -χ a b c
  gp : ∀ x₁ x₂ y₁ y₂ y₃ y₄ : E,
    let s : Fin 4 → SignType := ![χ x₁ x₂ y₁ * χ y₂ y₃ y₄, -(χ x₁ x₂ y₂ * χ y₁ y₃ y₄),
      χ x₁ x₂ y₃ * χ y₁ y₂ y₄, -(χ x₁ x₂ y₄ * χ y₁ y₂ y₃)]
    (∀ i, s i = 0) ∨ ((∃ i, s i = 1) ∧ (∃ i, s i = -1))

/-- `N` is a single-element extension of `M`, the new element being `none`. -/
def IsExtension {E : Type} (M : Chirotope3 E) (N : Chirotope3 (Option E)) : Prop :=
  ∀ a b c : E, N.χ (some a) (some b) (some c) = M.χ a b c

/-- Problem 17 (oriented-matroid form): two extensions with the same contraction at the new
element, up to a global sign, agree up to reorientation of the new element. -/
def problem17 : Prop :=
  ∀ (E : Type) (M : Chirotope3 E) (N₁ N₂ : Chirotope3 (Option E)),
    IsExtension M N₁ → IsExtension M N₂ →
    (∃ s : SignType, s ≠ 0 ∧
      ∀ a b : E, N₁.χ (some a) (some b) none = s * N₂.χ (some a) (some b) none) →
    ∃ s : SignType, s ≠ 0 ∧ ∀ x y z : Option E,
      N₁.χ x y z = (if none = x ∨ none = y ∨ none = z then s else 1) * N₂.χ x y z

lemma signType_eq_zero_of_eq_neg {x : SignType} (h : x = -x) : x = 0 := by cases x <;> simp_all

/-- Alternation: a chirotope vanishes when its first two arguments coincide. -/
lemma Chirotope3.eq_zero₁₂ {E : Type} (N : Chirotope3 E) (a c : E) : N.χ a a c = 0 :=
  signType_eq_zero_of_eq_neg (N.swap12 a a c)

/-- Alternation: a chirotope vanishes when its last two arguments coincide. -/
lemma Chirotope3.eq_zero₂₃ {E : Type} (N : Chirotope3 E) (a b : E) : N.χ a b b = 0 :=
  signType_eq_zero_of_eq_neg (N.swap23 a b b)

/-- Alternation: a chirotope vanishes when its first and last arguments coincide. -/
lemma Chirotope3.eq_zero₁₃ {E : Type} (N : Chirotope3 E) (a b : E) : N.χ a b a = 0 := by
  simpa [N.eq_zero₁₂] using N.swap23 a a b

/-- Alternation: moving the first argument to the last place is an even permutation. -/
lemma Chirotope3.eq_first {E : Type} (N : Chirotope3 E) (a b c : E) :
    N.χ c a b = N.χ a b c := by rw [N.swap12, N.swap23, neg_neg]

/-- Problem 17 holds in this form, by alternation alone: the triples without the new element
are those of `M`, those with exactly one are, up to the sign of a permutation, read off the
contraction, and those with two or three vanish. -/
theorem problem17_holds : problem17 := fun E M N₁ N₂ h₁ h₂ ⟨s, hs, hc⟩ => ⟨s, hs, by
  rintro (_ | a) (_ | b) (_ | c) <;> simp [Chirotope3.eq_zero₁₂, Chirotope3.eq_zero₂₃,
    Chirotope3.eq_zero₁₃, h₁ _ _ _, h₂ _ _ _, hc, N₁.swap23 (some _) (some _) none,
    N₂.swap23 (some _) (some _) none, N₁.eq_first (some _) (some _) none,
    N₂.eq_first (some _) (some _) none]⟩

end Problem17

end Grothendieck.Folder154
