module

public import Mathlib
public import Mathlib.Order.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card

@[expose] public section


/-!
# Folder 156-8: the axioms of a magasin, and the interior supports of the magasin of an ordered set

The modernised reading `transcripts/156-8/156-8.modern.tex` (chapter VIII of *Vers une
géométrie des formes*, « Analysis situs (quatrième mouture) », 26 June – 4 July 1986) starts from
a *magasin*: a set `𝓜` with an incidence `≤`, a refinement `≪` and an interior disjointness
`|∘|`, subject to Mag 1 – Mag 4 (page 7). Mag 2 asks that, for `X ≪ Y`, the faces `Z ≤ Y` with
`X ≪ Z` have a least element; `X ≪̊ Y` (interior incidence) means that this least element is `Y`.
Compatibility `X ≶ Y` asks `X' |∘| Y'` for all faces `X'` of `X` not under `Y` and `Y'` of `Y`
not under `X`. Pages 9 and 10 draw the first consequences; pages 89 to 102 compute everything
for the magasin of an ordered set `L` (points `P_x`, intervals `S_{a,b}`, `a < b`), whose
interior support of a part `Φ` is `supp° Φ = cosupp° (cosupp° Φ)`, `cosupp° Φ` the elements
interiorly disjoint from all of `Φ`.

Proved here:

* `IsMagasin`: Mag 1 – Mag 4 as on page 7. `intLe_refl`, `exists_intLe`: `≪̊` is reflexive and
  `X ≪ Y` gives a face `Y' ≤ Y` with `X ≪̊ Y'`. `compat_refl`, `compat_symm`, `compat_mono`:
  Proposition `1₀`. `dis_of_compat`: Proposition 2, `X ≠ Y`, `X ≶ Y` ⇒ `X |∘| Y`.
  `le_of_compat_of_intLe` (Corollary 1), `eq_of_compat_of_intLe` (Corollary 2),
  `ref_iff_le_of_compat` (Corollary 3, read with `≪`), `intLe_trans` (Proposition 3),
  `intLe_of_ref_of_ref` (the NB of page 10).
* `TwoSegments`: two segments of the plane, the end `q` of the first inside the second.
  `twoSegments_isMagasin`, `twoSegments_not_compat`: the margin's converse of Proposition 2
  fails. `twoSegments_cor3_as_transcribed`: Corollary 3 as transcribed, with `≪̊`, fails.
* `SubSegment`: the drawing of page 10, a segment `Y` inside a segment `Z`, its end `X`
  interior to `Z`. `subSegment_isMagasin`, `subSegment_nb`: `X ≪ Y ≪ Z`, `X ≪̊ Z`, `Y ≪̊ Z`,
  and not `X ≪̊ Y`.
* `Cell`, `dis`, `cosupp`, `supp`: the magasin of a partial order, pages 89–91.
  `supp_pt`: under Hypothesis H of page 99, `supp° {P_a} = {P_a}` for every `a`
  (Lemma 1, Corollary 1, pages 99–101).
* `Can`: the ordered set `a < b > c` of page 102. `can_cosupp_pa`, `can_supp_pa`: `cosupp° {P_a}
  = {P_b, S_{a,b}}` and `supp° {P_a} = {P_a}`; `can_cosupp_pb`; `can_supp_segment`:
  `cosupp° (S̃_{a,b}) = ∅`, `supp° (S̃_{a,b}) = 𝓜`, while `Omb (S_{a,b}) = S̃_{a,b}` and
  `card 𝓜 = 5`; `can_not_hypH`.
* `Anti`: a two-element antichain, where `supp° {P_a} = {P_a, P_c}`: Hypothesis H cannot simply
  be dropped from Corollary 1.

**What the formalisation finds.** The first consequences of Mag 1 – Mag 4 all hold, with two
corrections the reading had made and that the models confirm: the margin's equivalence
« `X |∘| Y ⇔ X ≶ Y` » is only an implication, and Corollary 3 holds with `≪`, not with `≪̊`.
On page 102 Grothendieck's own computation `supp° {P_a} = {P_a, P_b}` (margin « Canular ») is
wrong: `supp° {P_a} = {P_a}` there too, although `L` violates H; what the example does show is
that the interval case of Lemma 1 fails, `supp° (S̃_{a,b}) = 𝓜 ≠ Omb (S_{a,b})`. The axioms of a
magasin are not checked for the magasin of an ordered set; the finite models check them.
-/

namespace Grothendieck.Folder156_8

/-! ## The axioms of a magasin (page 7) and the first consequences (pages 9 and 10) -/

section Magasin

variable {M : Type*}

/-- Interior incidence `X ≪̊ Y`: `X ≪ Y`, and `Y` is the only face `Z ≤ Y` with `X ≪ Z`. -/
def IntLe (le ref : M → M → Prop) (X Y : M) : Prop :=
  ref X Y ∧ ∀ Z, le Z Y → ref X Z → Z = Y

/-- Mag 1 – Mag 4 of page 7, for an incidence `le`, a refinement `ref` and an interior
disjointness `dis`. -/
structure IsMagasin (le ref dis : M → M → Prop) : Prop where
  le_refl : ∀ X, le X X
  le_trans : ∀ X Y Z, le X Y → le Y Z → le X Z
  le_antisymm : ∀ X Y, le X Y → le Y X → X = Y
  ref_refl : ∀ X, ref X X
  ref_trans : ∀ X Y Z, ref X Y → ref Y Z → ref X Z
  ref_antisymm : ∀ X Y, ref X Y → ref Y X → X = Y
  le_ref : ∀ X Y, le X Y → ref X Y
  mag2 : ∀ X Y, ref X Y → ∃ Z, le Z Y ∧ ref X Z ∧ ∀ W, le W Y → ref X W → le Z W
  dis_symm : ∀ X Y, dis X Y → dis Y X
  dis_irrefl : ∀ X, ¬ dis X X
  mag3 : ∀ X Y X' Y', dis X Y → IntLe le ref X' X → IntLe le ref Y' Y → dis X' Y'
  mag4 : ∀ X Y Z, le Y X → le Z X → Y ≠ Z → dis Y Z

/-- Compatibility `X ≶ Y`: every face of `X` not under `Y` is interiorly disjoint from every
face of `Y` not under `X`. -/
def Compat (le dis : M → M → Prop) (X Y : M) : Prop :=
  ∀ X' Y', le X' X → ¬ le X' Y → le Y' Y → ¬ le Y' X → dis X' Y'

variable {le ref dis : M → M → Prop}

theorem intLe_refl (h : IsMagasin le ref dis) (X : M) : IntLe le ref X X :=
  ⟨h.ref_refl X, fun _ hZ hXZ => h.ref_antisymm _ _ (h.le_ref _ _ hZ) hXZ⟩

/-- The least element of Mag 2 is a face `Y' ≤ Y` with `X ≪̊ Y'`. -/
theorem exists_intLe (h : IsMagasin le ref dis) {X Y : M} (hXY : ref X Y) :
    ∃ Y', le Y' Y ∧ IntLe le ref X Y' := by
  obtain ⟨Z, hZY, hXZ, hmin⟩ := h.mag2 X Y hXY
  exact ⟨Z, hZY, hXZ, fun W hWZ hXW =>
    h.le_antisymm _ _ hWZ (hmin W (h.le_trans _ _ _ hWZ hZY) hXW)⟩

/-- Proposition `1₀` a), reflexivity. -/
theorem compat_refl (X : M) : Compat le dis X X :=
  fun _ _ h1 h2 _ _ => (h2 h1).elim

/-- Proposition `1₀` a), symmetry. -/
theorem compat_symm (h : IsMagasin le ref dis) {X Y : M} (hXY : Compat le dis X Y) :
    Compat le dis Y X :=
  fun Y' X' h1 h2 h3 h4 => h.dis_symm _ _ (hXY X' Y' h3 h4 h1 h2)

/-- Proposition `1₀` b): compatibility passes to faces. -/
theorem compat_mono (h : IsMagasin le ref dis) {X Y X' Y' : M} (hX : le X' X) (hY : le Y' Y)
    (hXY : Compat le dis X Y) : Compat le dis X' Y' := by
  intro X'' Y'' h1 h2 h3 h4
  have hne : X'' ≠ Y'' := fun he => h2 (he ▸ h3)
  by_cases hXY' : le X'' Y
  · exact h.mag4 Y X'' Y'' hXY' (h.le_trans _ _ _ h3 hY) hne
  by_cases hYX : le Y'' X
  · exact h.mag4 X X'' Y'' (h.le_trans _ _ _ h1 hX) hYX hne
  exact hXY X'' Y'' (h.le_trans _ _ _ h1 hX) hXY' (h.le_trans _ _ _ h3 hY) hYX

/-- **Proposition 2** (margin of page 9), in the direction that holds: two distinct compatible
elements are interiorly disjoint. -/
theorem dis_of_compat (h : IsMagasin le ref dis) {X Y : M} (hne : X ≠ Y)
    (hXY : Compat le dis X Y) : dis X Y := by
  by_cases h1 : le X Y
  · exact h.mag4 Y X Y h1 (h.le_refl Y) hne
  by_cases h2 : le Y X
  · exact h.mag4 X X Y (h.le_refl X) h2 hne
  exact hXY X Y (h.le_refl X) h1 (h.le_refl Y) h2

/-- **Corollary 1** (page 9): if `X ≶ Y`, `Z ≪̊ X` and `Z ≪ Y`, then `X ≤ Y` (so `X ≪ Y`). -/
theorem le_of_compat_of_intLe (h : IsMagasin le ref dis) {X Y Z : M}
    (hXY : Compat le dis X Y) (hZX : IntLe le ref Z X) (hZY : ref Z Y) : le X Y := by
  obtain ⟨Y', hY'Y, hZY'⟩ := exists_intLe h hZY
  have hc : Compat le dis X Y' := compat_mono h (h.le_refl X) hY'Y hXY
  by_cases he : X = Y'
  · exact he ▸ hY'Y
  exact (h.dis_irrefl Z (h.mag3 X Y' Z Z (dis_of_compat h he hc) hZX hZY')).elim

/-- Corollary 1 as an equivalence. -/
theorem ref_iff_of_compat_of_intLe (h : IsMagasin le ref dis) {X Y Z : M}
    (hXY : Compat le dis X Y) (hZX : IntLe le ref Z X) : ref Z Y ↔ ref X Y :=
  ⟨fun hZY => h.le_ref _ _ (le_of_compat_of_intLe h hXY hZX hZY),
    fun hX => h.ref_trans _ _ _ hZX.1 hX⟩

/-- **Corollary 2** (page 9). -/
theorem eq_of_compat_of_intLe (h : IsMagasin le ref dis) {X Y Z : M}
    (hZX : IntLe le ref Z X) (hZY : IntLe le ref Z Y) (hXY : Compat le dis X Y) : X = Y :=
  h.le_antisymm _ _ (le_of_compat_of_intLe h hXY hZX hZY.1)
    (le_of_compat_of_intLe h (compat_symm h hXY) hZY hZX.1)

/-- **Corollary 3** (page 10), read with `≪`: between compatible elements, refinement and
incidence coincide. -/
theorem ref_iff_le_of_compat (h : IsMagasin le ref dis) {X Y : M} (hXY : Compat le dis X Y) :
    ref X Y ↔ le X Y :=
  ⟨le_of_compat_of_intLe h hXY (intLe_refl h X), h.le_ref X Y⟩

/-- **Proposition 3** (page 10): `≪̊` is transitive. -/
theorem intLe_trans (h : IsMagasin le ref dis) {X Y Z : M} (hXY : IntLe le ref X Y)
    (hYZ : IntLe le ref Y Z) : IntLe le ref X Z := by
  obtain ⟨Z', hZ'Z, hXZ'⟩ := exists_intLe h (h.ref_trans _ _ _ hXY.1 hYZ.1)
  by_cases he : Z' = Z
  · exact he ▸ hXZ'
  have h1 : dis Z' Z := h.mag4 Z Z' Z hZ'Z (h.le_refl Z) he
  have h2 : dis X Y := h.mag3 Z' Z X Y h1 hXZ' hYZ
  exact (h.dis_irrefl X (h.mag3 X Y X X h2 (intLe_refl h X) hXY)).elim

/-- The NB of page 10: `X ≪ Y ≪ Z` and `X ≪̊ Z` give `Y ≪̊ Z`. -/
theorem intLe_of_ref_of_ref (h : IsMagasin le ref dis) {X Y Z : M} (hXY : ref X Y)
    (hYZ : ref Y Z) (hXZ : IntLe le ref X Z) : IntLe le ref Y Z :=
  ⟨hYZ, fun W hWZ hYW => hXZ.2 W hWZ (h.ref_trans _ _ _ hXY hYW)⟩

instance [Fintype M] [DecidableEq M] [DecidableRel le] [DecidableRel ref] :
    DecidableRel (IntLe le ref) :=
  fun X Y => inferInstanceAs (Decidable (ref X Y ∧ ∀ Z, le Z Y → ref X Z → Z = Y))

instance [Fintype M] [DecidableRel le] [DecidableRel dis] : DecidableRel (Compat le dis) :=
  fun X Y => inferInstanceAs
    (Decidable (∀ X' Y', le X' X → ¬ le X' Y → le Y' Y → ¬ le Y' X → dis X' Y'))

end Magasin

/-! ## Two segments of the plane (footnote to page 9) -/

section TwoSegments

/-- `0 = p`, `1 = q`, `2 = r`, `3 = s`, `4 = X = [p, q]`, `5 = Y = [r, s]`, with `q` inside
`Y`. -/
abbrev TwoSegments := Fin 6

/-- Faces. -/
def tsLe (x y : TwoSegments) : Prop :=
  x = y ∨ ((x = 0 ∨ x = 1) ∧ y = 4) ∨ ((x = 2 ∨ x = 3) ∧ y = 5)

/-- Containment: faces, and `q ⊂ Y`. -/
def tsRef (x y : TwoSegments) : Prop := tsLe x y ∨ (x = 1 ∧ y = 5)

/-- Disjoint interiors: every pair of distinct cells, except `q` and `Y`. -/
def tsDis (x y : TwoSegments) : Prop :=
  x ≠ y ∧ ¬ (x = 1 ∧ y = 5) ∧ ¬ (x = 5 ∧ y = 1)

instance : DecidableRel tsLe := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel tsRef := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel tsDis := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem twoSegments_isMagasin : IsMagasin tsLe tsRef tsDis := by
  constructor <;> decide

/-- **The margin's converse of Proposition 2 fails**: `X ≠ Y` and `X |∘| Y`, but `X` and `Y`
are not compatible. -/
theorem twoSegments_not_compat : (4 : TwoSegments) ≠ 5 ∧ tsDis 4 5 ∧ ¬ Compat tsLe tsDis 4 5 := by
  decide

/-- **Corollary 3 as transcribed fails**: `p ≶ X` and `p ≤ X`, but not `p ≪̊ X`. -/
theorem twoSegments_cor3_as_transcribed :
    Compat tsLe tsDis 0 4 ∧ tsLe 0 4 ∧ ¬ IntLe tsLe tsRef 0 4 := by
  decide

end TwoSegments

/-! ## The drawing of page 10 -/

section SubSegment

/-- `0, 3` the ends of `Z = 5`, `1, 2` the ends of `Y = 4`, with `Y` inside `Z`. -/
abbrev SubSegment := Fin 6

def ssLe (x y : SubSegment) : Prop :=
  x = y ∨ ((x = 1 ∨ x = 2) ∧ y = 4) ∨ ((x = 0 ∨ x = 3) ∧ y = 5)

def ssRef (x y : SubSegment) : Prop := ssLe x y ∨ ((x = 1 ∨ x = 2 ∨ x = 4) ∧ y = 5)

/-- Disjoint interiors: distinct cells, except `Z` against `1`, `2` and `Y`. -/
def ssDis (x y : SubSegment) : Prop :=
  x ≠ y ∧ ¬ ((x = 1 ∨ x = 2 ∨ x = 4) ∧ y = 5) ∧ ¬ (x = 5 ∧ (y = 1 ∨ y = 2 ∨ y = 4))

instance : DecidableRel ssLe := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel ssRef := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidableRel ssDis := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem subSegment_isMagasin : IsMagasin ssLe ssRef ssDis := by
  constructor <;> decide

/-- **The NB of page 10**: with `X = 2`, `X ≪ Y ≪ Z` and `X ≪̊ Z`, hence `Y ≪̊ Z`, but not
`X ≪̊ Y`. -/
theorem subSegment_nb :
    ssRef 2 4 ∧ ssRef 4 5 ∧ IntLe ssLe ssRef 2 5 ∧ IntLe ssLe ssRef 4 5 ∧
      ¬ IntLe ssLe ssRef 2 4 := by
  decide

end SubSegment

/-! ## The magasin of an ordered set (pages 89 to 102) -/

section OrderedSet

variable {L : Type*} [PartialOrder L]

/-- The elements of the magasin of `L`: the points `P_x` and the intervals `S_{a,b}`, `a < b`. -/
abbrev Cell (L : Type*) [PartialOrder L] := L ⊕ {p : L × L // p.1 < p.2}

/-- The point `P_x`. -/
abbrev pt (x : L) : Cell L := Sum.inl x

/-- The interval `S_{a,b}`. -/
abbrev iv (a b : L) (h : a < b) : Cell L := Sum.inr ⟨(a, b), h⟩

/-- Interior disjointness, page 89. -/
def dis : Cell L → Cell L → Prop
  | .inl x, .inl y => x < y ∨ y < x
  | .inl x, .inr s => x ≤ s.1.1 ∨ s.1.2 ≤ x
  | .inr s, .inl x => x ≤ s.1.1 ∨ s.1.2 ≤ x
  | .inr s, .inr t => s.1.2 ≤ t.1.1 ∨ t.1.2 ≤ s.1.1

theorem dis_symm {X Y : Cell L} (h : dis X Y) : dis Y X := by
  rcases X with x | s <;> rcases Y with y | t <;> simp only [dis] at h ⊢ <;> tauto

theorem dis_irrefl (X : Cell L) : ¬ dis X X := by
  rcases X with x | ⟨⟨a, b⟩, hab⟩ <;> simp only [dis, lt_irrefl, or_self, not_false_eq_true]
  exact fun h => lt_irrefl _ (lt_of_lt_of_le hab h)

/-- `cosupp° Φ`: the elements interiorly disjoint from every element of `Φ`. -/
def cosupp (Φ : Set (Cell L)) : Set (Cell L) := {X | ∀ Y ∈ Φ, dis Y X}

/-- `supp° Φ = cosupp° (cosupp° Φ)`. -/
def supp (Φ : Set (Cell L)) : Set (Cell L) := cosupp (cosupp Φ)

theorem subset_supp (Φ : Set (Cell L)) : Φ ⊆ supp Φ :=
  fun _ hX _ hY => dis_symm (hY _ hX)

/-- `cosupp° Φ ∩ supp° Φ = ∅`, page 101. -/
theorem not_mem_cosupp_of_mem_supp {Φ : Set (Cell L)} {X : Cell L} (hX : X ∈ supp Φ) :
    X ∉ cosupp Φ :=
  fun h => dis_irrefl X (hX X h)

/-- **Hypothesis H** (page 99): a) either `L` has a least element or every element strictly
majorises another; b) the dual statement. -/
def HypH (L : Type*) [PartialOrder L] : Prop :=
  ((∃ m : L, ∀ x, m ≤ x) ∨ ∀ x : L, ∃ y, y < x) ∧ ((∃ m : L, ∀ x, x ≤ m) ∨ ∀ x : L, ∃ y, x < y)

theorem HypH.exists_lt (H : HypH L) {a : L} (ha : ¬ ∀ x, a ≤ x) : ∃ x, x < a := by
  rcases H.1 with ⟨m, hm⟩ | h
  · refine ⟨m, lt_of_le_of_ne (hm a) ?_⟩
    rintro rfl
    exact ha hm
  · exact h a

theorem HypH.exists_gt (H : HypH L) {a : L} (ha : ¬ ∀ x, x ≤ a) : ∃ y, a < y := by
  rcases H.2 with ⟨m, hm⟩ | h
  · refine ⟨m, lt_of_le_of_ne (hm a) ?_⟩
    rintro rfl
    exact ha hm
  · exact h a

/-- **Lemma 1 for a point, Corollary 1** (pages 99–101): under Hypothesis H, the interior
support of a point is the point itself. -/
theorem supp_pt (H : HypH L) (a : L) : supp {pt a} = {pt a} := by
  refine Set.Subset.antisymm (fun X hX => ?_) (subset_supp _)
  have hn : ¬ dis (pt a) X := fun h => not_mem_cosupp_of_mem_supp hX (by simpa [cosupp] using h)
  have hall : ∀ Y, dis (pt a) Y → dis Y X := fun Y hY => hX Y (by simpa [cosupp] using hY)
  rw [Set.mem_singleton_iff]
  by_cases hmin : ∀ x, a ≤ x
  · rcases X with z | ⟨⟨c, d⟩, hcd⟩
    · simp only [dis, not_or] at hn
      rcases eq_or_lt_of_le (hmin z) with he | hlt
      · exact congrArg Sum.inl he.symm
      · exact (hn.1 hlt).elim
    · simp only [dis, not_or] at hn
      exact (hn.1 (hmin c)).elim
  by_cases hmax : ∀ x, x ≤ a
  · rcases X with z | ⟨⟨c, d⟩, hcd⟩
    · simp only [dis, not_or] at hn
      rcases eq_or_lt_of_le (hmax z) with he | hlt
      · exact congrArg Sum.inl he
      · exact (hn.2 hlt).elim
    · simp only [dis, not_or] at hn
      exact (hn.2 (hmax d)).elim
  obtain ⟨x, hxa⟩ := H.exists_lt hmin
  obtain ⟨y, hay⟩ := H.exists_gt hmax
  have h1 := hall (iv x a hxa) (by simp [dis])
  have h2 := hall (iv a y hay) (by simp [dis])
  rcases X with z | ⟨⟨c, d⟩, hcd⟩
  · simp only [dis, not_or] at hn h1 h2
    rcases h1 with h1 | h1
    · exact (hn.2 (lt_of_le_of_lt h1 hxa)).elim
    rcases h2 with h2 | h2
    · exact congrArg Sum.inl (le_antisymm h2 h1)
    · exact (hn.1 (lt_of_lt_of_le hay h2)).elim
  · simp only [dis, not_or] at hn h1
    rcases h1 with h1 | h1
    · exact (hn.1 h1).elim
    · exact (hn.2 (h1.trans hxa.le)).elim

variable [DecidableRel (α := L) (· ≤ ·)] [DecidableRel (α := L) (· < ·)]

instance : DecidableRel (dis (L := L))
  | .inl x, .inl y => inferInstanceAs (Decidable (x < y ∨ y < x))
  | .inl x, .inr s => inferInstanceAs (Decidable (x ≤ s.1.1 ∨ s.1.2 ≤ x))
  | .inr s, .inl x => inferInstanceAs (Decidable (x ≤ s.1.1 ∨ s.1.2 ≤ x))
  | .inr s, .inr t => inferInstanceAs (Decidable (s.1.2 ≤ t.1.1 ∨ t.1.2 ≤ s.1.1))

variable [Fintype L] [DecidableEq L]

/-- `cosupp°` on finite parts of a finite magasin. -/
def cosuppF (Φ : Finset (Cell L)) : Finset (Cell L) :=
  Finset.univ.filter fun X => ∀ Y ∈ Φ, dis Y X

/-- `supp°` on finite parts of a finite magasin. -/
def suppF (Φ : Finset (Cell L)) : Finset (Cell L) := cosuppF (cosuppF Φ)

theorem coe_cosuppF (Φ : Finset (Cell L)) : (cosuppF Φ : Set (Cell L)) = cosupp Φ := by
  ext X
  simp [cosuppF, cosupp]

theorem coe_suppF (Φ : Finset (Cell L)) : (suppF Φ : Set (Cell L)) = supp Φ := by
  rw [suppF, coe_cosuppF, coe_cosuppF, supp]

/-- The underlying part `|X|` of `L`: `{x}` for `P_x`, `[a, b]` for `S_{a,b}`. -/
def carrier : Cell L → Finset L
  | .inl x => {x}
  | .inr s => Finset.univ.filter fun z => s.1.1 ≤ z ∧ z ≤ s.1.2

/-- `Omb Y = {Z | |Z| ⊂ |Y|}` (pages 91 and 99). -/
def omb (Y : Cell L) : Finset (Cell L) := Finset.univ.filter fun X => carrier X ⊆ carrier Y

end OrderedSet

/-! ## The « canular » of page 102 -/

section Canular

/-- The ordered set of page 102: `a < b` and `c < b` only. -/
inductive Can | a | b | c
  deriving DecidableEq

namespace Can

instance : Fintype Can := ⟨{a, b, c}, fun x => by cases x <;> decide⟩

def leB : Can → Can → Bool
  | a, a | b, b | c, c | a, b | c, b => true
  | _, _ => false

instance : LE Can := ⟨fun x y => leB x y = true⟩

instance : DecidableRel (α := Can) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (leB x y = true))

instance : PartialOrder Can where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := Can) (· < ·) :=
  fun x y => inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))

theorem a_lt_b : a < b := by decide
theorem c_lt_b : c < b := by decide

end Can

open Can

/-- `P_a`, `P_b`, `P_c`, `S_{a,b}`, `S_{c,b}`. -/
abbrev Pa : Cell Can := pt Can.a
abbrev Pb : Cell Can := pt Can.b
abbrev Pc : Cell Can := pt Can.c
abbrev Sab : Cell Can := iv Can.a Can.b a_lt_b
abbrev Scb : Cell Can := iv Can.c Can.b c_lt_b

/-- `cosupp° {P_a} = {P_b, S_{a,b}}`; the page adds `S_{c,b}`. -/
theorem can_cosupp_pa : cosuppF ({Pa} : Finset (Cell Can)) = {Pb, Sab} := by decide

/-- **`supp° {P_a} = {P_a}`**, not `{P_a, P_b}` as on the page. -/
theorem can_supp_pa : suppF ({Pa} : Finset (Cell Can)) = {Pa} := by decide

/-- First line of page 102: `cosupp° {P_b} = 𝓜 ∖ {P_b}`. -/
theorem can_cosupp_pb : cosuppF ({Pb} : Finset (Cell Can)) = Finset.univ \ {Pb} := by decide

/-- **The interval case of Lemma 1 fails**: `cosupp° (S̃_{a,b}) = ∅` and `supp° (S̃_{a,b}) = 𝓜`,
while `Omb (S_{a,b}) = S̃_{a,b} = {P_a, P_b, S_{a,b}}` and `𝓜` has five elements. -/
theorem can_supp_segment :
    cosuppF ({Pa, Pb, Sab} : Finset (Cell Can)) = ∅ ∧
      suppF ({Pa, Pb, Sab} : Finset (Cell Can)) = Finset.univ ∧
      omb Sab = {Pa, Pb, Sab} ∧ Fintype.card (Cell Can) = 5 ∧
      (Finset.univ : Finset (Cell Can)) = {Pa, Pb, Sab, Scb, Pc} := by
  decide

/-- The ordered set of page 102 violates Hypothesis H. -/
theorem can_not_hypH : ¬ HypH Can := by
  unfold HypH
  decide

end Canular

/-! ## A two-element antichain -/

section Antichain

/-- Two incomparable elements. -/
inductive Anti | a | c
  deriving DecidableEq

namespace Anti

instance : Fintype Anti := ⟨{a, c}, fun x => by cases x <;> decide⟩

instance : LE Anti := ⟨fun x y => x = y⟩

instance : DecidableRel (α := Anti) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x = y))

instance : PartialOrder Anti where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableRel (α := Anti) (· < ·) :=
  fun x y => inferInstanceAs (Decidable (x ≤ y ∧ ¬ y ≤ x))

end Anti

/-- Without Hypothesis H, Corollary 1 can fail: in a two-element antichain,
`supp° {P_a} = {P_a, P_c}`. -/
theorem anti_supp_pa :
    suppF ({pt Anti.a} : Finset (Cell Anti)) = {pt Anti.a, pt Anti.c} ∧ ¬ HypH Anti := by
  unfold HypH
  decide

end Antichain

end Grothendieck.Folder156_8
