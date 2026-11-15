module

public import Mathlib
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section


/-!
# Folder 81, pages 31–39 and 45–47: non-parallel decompositions and their ordered quartets

The modernised reading `transcripts/81/81.modern.tex` (§ V, « Décompositions n-aires : la
Version II », and § VI, « Relations d'équivalence non parallèles ») works with *binary
decompositions* of a space `X`: pairs of hemispheres `Σ⁺, Σ⁻` with `Σ⁺ ∪ Σ⁻ = X`, both non-empty
and distinct (page 31, (1)–(3)). Two of them are *non parallel* when they are distinct and one
hemisphere of each can be chosen disjoint from one of the other (page 32, (10)) — two chords of
a disc that do not cross. For a family of pairwise non-parallel decompositions, page 37 puts on
the disjoint union `C` of the index pairs the relation (26), `x < y` when `x`, `y` belong to
different decompositions and `Σˣ ∩ Σ^{σ y} = ∅`, with the margin « il faut vérifier que c'est
transitif … d'ordre ». Page 38 abstracts the result as a *quartette ordonné* (a finite set with
a fixed-point-free involution `σ` and an order such that `x, y` are comparable iff `σ x, y` are
not, and `σ` reverses the order), and page 39 states:

> Proposition. Soit (C, σ, <) un quartette ordonné. Alors pour tout x ∈ C, C_{≥ x} et C_{≤ x}
> sont *totalement* ordonnés.

The proof on the page stops mid-sentence. Proved here:

* `disjoint_unique` (proposition of page 34): two non-parallel decompositions have exactly one
  pair of disjoint hemispheres.
* `isQuartette_family` (pages 37 and 38): for any family of pairwise non-parallel binary
  decompositions, relation (26) is irreflexive and transitive, `σ` reverses it, and `x, y` are
  comparable iff `σ x, y` are not: the margin's transitivity holds and `C` is an ordered
  quartet. Closedness of the hemispheres is never used.
* `interval_comp`: in any ordered quartet every interval `[x, z]` is a chain (condition a)
  alone suffices).
* `tripod_isQuartette`, `tripod_not_chain` (counterexample to page 39): the six-element quartet
  of three chords around a triangle, `c₁, c₂, c₃` the caps and `c₁', c₂', c₃'` the large sides,
  with `cᵢ < cⱼ'` (`i ≠ j`) only; `C_{≥ c₁} = {c₁, c₂', c₃'}` is not a chain.
  `chords_family_not_chain`: the same configuration realised by three binary decompositions of
  the seven-point model of the disc (a triangle, three chords, three caps), through
  `isQuartette_family`.
* `rev_not_of_comp`: condition b) (`σ` reverses the order), struck on page 38, does not follow
  from condition a).
* `page47_cores` (the NB of page 47): on the hexagon `a₁, b, a₂, a₂', b', a₁'` (three parallel
  chords), the two families `sigma₁`, `sigma₂` are distinct sets of segments satisfying
  (σ₁)–(σ₃) with
  the same partition into cores `{a₁, a₁'}, {b, b'}, {a₂, a₂'}`: the family is not recovered from
  the partition, as the page says.

**What the formalisation finds.** The proposition of page 39 is false as stated: in the quartet
of three chords around a triangle — the configuration whose graph page 11 draws as a heavy
tripod — `C_{≥ c₁}` contains the incomparable `c₂'` and `c₃'`. What holds is that every interval
is a chain. The transitivity asked in the margin of page 38 holds, and the order of a
non-parallel family is a quartet. The NB of page 47 is correct.
-/

namespace Grothendieck.Folder81

/-! ## Ordered quartets (page 38) -/

section Quartette

variable {C : Type*}

/-- `x` and `y` are comparable for the strict relation `lt`. -/
def Comp (lt : C → C → Prop) (x y : C) : Prop := x = y ∨ lt x y ∨ lt y x

/-- The large relation of `lt`. -/
def Le (lt : C → C → Prop) (x y : C) : Prop := x = y ∨ lt x y

instance [DecidableEq C] (lt : C → C → Prop) [DecidableRel lt] : DecidableRel (Comp lt) :=
  fun _ _ => by unfold Comp; infer_instance

instance [DecidableEq C] (lt : C → C → Prop) [DecidableRel lt] : DecidableRel (Le lt) :=
  fun _ _ => by unfold Le; infer_instance

/-- Page 38, *quartette ordonné*: a fixed-point-free involution `σ` and a strict order `lt`
such that a) `x, y` are comparable iff `σ x, y` are not, and b) `σ` reverses the order. -/
structure IsQuartette (σ : C → C) (lt : C → C → Prop) : Prop where
  invol : ∀ x, σ (σ x) = x
  ne_self : ∀ x, σ x ≠ x
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ x y z, lt x y → lt y z → lt x z
  comp_iff : ∀ x y, Comp lt x y ↔ ¬ Comp lt (σ x) y
  rev : ∀ x y, lt x y → lt (σ y) (σ x)

variable {σ : C → C} {lt : C → C → Prop}

theorem Comp.symm {x y : C} (h : Comp lt x y) : Comp lt y x := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem Le.comp {x y : C} (h : Le lt x y) : Comp lt x y := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem Le.trans' (htr : ∀ x y z, lt x y → lt y z → lt x z) {x y z : C}
    (h₁ : Le lt x y) (h₂ : Le lt y z) : Le lt x z := by
  rcases h₁ with rfl | h₁
  · exact h₂
  rcases h₂ with rfl | h₂
  · exact Or.inr h₁
  · exact Or.inr (htr _ _ _ h₁ h₂)

/-- In an ordered quartet every interval `[x, z]` is a chain; only condition a) is used. -/
theorem interval_comp (h : IsQuartette σ lt) {x y y' z : C} (hxy : Le lt x y)
    (hxy' : Le lt x y') (hyz : Le lt y z) (hy'z : Le lt y' z) : Comp lt y y' := by
  by_contra hn
  have h1 : Comp lt (σ y) y' := by
    by_contra h2
    exact hn ((h.comp_iff y y').2 h2)
  have hyz' := (h.comp_iff y z).1 hyz.comp
  have hyx' := (h.comp_iff y x).1 hxy.comp.symm
  rcases h1 with h1 | h1 | h1
  · exact hyz' (by rw [h1]; exact hy'z.comp)
  · exact hyz' (Le.trans' h.trans (Or.inr h1) hy'z).comp
  · exact hyx' (Le.trans' h.trans hxy' (Or.inr h1)).comp.symm

end Quartette

/-! ## The counterexample to page 39: three chords around a triangle -/

/-- The involution of the tripod quartet: `cᵢ = i ↦ cᵢ' = i + 3` and back. -/
def tσ (x : Fin 6) : Fin 6 := x + 3

/-- The order of the tripod quartet: `cᵢ < cⱼ'` for `i ≠ j`, and nothing else. -/
def tlt (x y : Fin 6) : Prop := x.val < 3 ∧ 3 ≤ y.val ∧ y.val ≠ x.val + 3

instance : DecidableRel tlt := fun _ _ => by unfold tlt; infer_instance

theorem tripod_isQuartette : IsQuartette tσ tlt where
  invol := by decide
  ne_self := by decide
  irrefl := by decide
  trans := by decide
  comp_iff := by decide
  rev := by decide

/-- Page 39 fails: `c₁ < c₂'`, `c₁ < c₃'`, and `c₂'`, `c₃'` are incomparable. -/
theorem tripod_not_chain : tlt 0 4 ∧ tlt 0 5 ∧ ¬ Comp tlt 4 5 := by decide

theorem page39_false :
    ¬ ∀ x y z : Fin 6, Le tlt x y → Le tlt x z → Comp tlt y z := by
  intro h
  exact tripod_not_chain.2.2 (h 0 4 5 (Or.inr tripod_not_chain.1) (Or.inr tripod_not_chain.2.1))

/-- Condition b) does not follow from a): on `{x, σx, y, σy}` with only `x < y`, `σx < σy`. -/
def rσ (x : Fin 4) : Fin 4 := if x.val % 2 = 0 then x + 1 else x - 1

def rlt (x y : Fin 4) : Prop := (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3)

instance : DecidableRel rlt := fun _ _ => by unfold rlt; infer_instance

theorem rev_not_of_comp :
    (∀ x, rσ (rσ x) = x) ∧ (∀ x, rσ x ≠ x) ∧ (∀ x, ¬ rlt x x) ∧
    (∀ x y z, rlt x y → rlt y z → rlt x z) ∧
    (∀ x y, Comp rlt x y ↔ ¬ Comp rlt (rσ x) y) ∧
    ¬ ∀ x y, rlt x y → rlt (rσ y) (rσ x) := by decide

/-! ## Binary decompositions and non-parallel families (pages 31–38) -/

section Decomp

variable {X : Type*}

/-- Page 31, (1)–(3): two hemispheres covering `X`, non-empty and distinct. -/
structure Decomp (X : Type*) where
  hem : Bool → Set X
  cover : hem true ∪ hem false = Set.univ
  nonempty : ∀ e, (hem e).Nonempty
  ne : hem true ≠ hem false

/-- Two decompositions are the same unordered pair of hemispheres. -/
def Same (P Q : Decomp X) : Prop :=
  (P.hem true = Q.hem true ∧ P.hem false = Q.hem false) ∨
    (P.hem true = Q.hem false ∧ P.hem false = Q.hem true)

/-- Page 32, (10): distinct, with one hemisphere of each disjoint from one of the other. -/
def NonParallel (P Q : Decomp X) : Prop :=
  ¬ Same P Q ∧ ∃ e f, P.hem e ∩ Q.hem f = ∅

theorem Decomp.mem_not (P : Decomp X) (e : Bool) {x : X} (hx : x ∉ P.hem e) :
    x ∈ P.hem (!e) := by
  have : x ∈ P.hem true ∪ P.hem false := P.cover ▸ Set.mem_univ x
  cases e <;> simp_all

/-- (11): a hemisphere disjoint from `Q.hem f` lies in the other hemisphere of `Q`. -/
theorem subset_of_inter {P Q : Decomp X} {e f : Bool} (h : P.hem e ∩ Q.hem f = ∅) :
    P.hem e ⊆ Q.hem (!f) := by
  intro x hx
  refine Q.mem_not f fun hq => ?_
  have : x ∈ P.hem e ∩ Q.hem f := ⟨hx, hq⟩
  rw [h] at this
  exact this

theorem same_of_eq {P Q : Decomp X} {e f : Bool} (h₁ : P.hem e = Q.hem f)
    (h₂ : P.hem (!e) = Q.hem (!f)) : Same P Q := by
  cases e <;> cases f <;> simp_all [Same]

theorem inter_self_ne {P Q : Decomp X} {e f : Bool} (h : P.hem e ∩ Q.hem f = ∅) :
    P.hem e ∩ Q.hem (!f) ≠ ∅ := by
  rw [Set.inter_eq_left.2 (subset_of_inter h)]
  exact (P.nonempty e).ne_empty

/-- Proposition of page 34: the disjoint pair of hemispheres is unique. -/
theorem disjoint_unique {P Q : Decomp X} (hPQ : NonParallel P Q) {e f e' f' : Bool}
    (h : P.hem e ∩ Q.hem f = ∅) (h' : P.hem e' ∩ Q.hem f' = ∅) : e' = e ∧ f' = f := by
  rcases Bool.eq_or_eq_not e' e with he | he <;>
    rcases Bool.eq_or_eq_not f' f with hf | hf <;> rw [he, hf] at h'
  · exact ⟨he, hf⟩
  · exact absurd h' (inter_self_ne h)
  · have h1 : Q.hem f ∩ P.hem e = ∅ := by rw [Set.inter_comm]; exact h
    have := inter_self_ne h1
    rw [Set.inter_comm] at this
    exact absurd h' this
  · exfalso
    apply hPQ.1
    have a1 := subset_of_inter h
    have a2 := subset_of_inter h'
    have b1 := subset_of_inter (P := Q) (Q := P) (by rw [Set.inter_comm]; exact h)
    have b2 := subset_of_inter (P := Q) (Q := P) (by rw [Set.inter_comm]; exact h')
    simp only [Bool.not_not] at a2 b2
    exact same_of_eq (e := e) (f := !f) (a1.antisymm b2) (by
      rw [Bool.not_not]; exact a2.antisymm b1)

variable {A : Type*} (F : A → Decomp X)

/-- The involution of `C = A × Bool` (page 37, (25)). -/
def famσ (x : A × Bool) : A × Bool := (x.1, !x.2)

/-- Relation (26) of page 38. -/
def famLt (x y : A × Bool) : Prop :=
  x.1 ≠ y.1 ∧ (F x.1).hem x.2 ∩ (F y.1).hem (!y.2) = ∅

/-- Pages 37 and 38: the relation (26) of a pairwise non-parallel family is a strict order,
reversed by `σ`, and `x, y` are comparable iff `σ x, y` are not: an ordered quartet. -/
theorem isQuartette_family (hF : Pairwise fun a b => NonParallel (F a) (F b)) :
    IsQuartette famσ (famLt F) where
  invol x := by simp [famσ]
  ne_self x h := by
    have := congrArg Prod.snd h
    simp [famσ] at this
  irrefl x h := h.1 rfl
  trans := by
    rintro ⟨a, e⟩ ⟨b, f⟩ ⟨c, g⟩ ⟨hab, h1⟩ ⟨hbc, h2⟩
    dsimp only at *
    have hsub : (F a).hem e ⊆ (F b).hem f := by
      simpa using subset_of_inter h1
    have h3 : (F a).hem e ∩ (F c).hem (!g) = ∅ := by
      apply Set.eq_empty_of_subset_empty
      rw [← h2]
      exact Set.inter_subset_inter_left _ hsub
    refine ⟨fun hac => ?_, h3⟩
    subst hac
    rcases Bool.eq_or_eq_not g e with rfl | rfl
    · have h2' : (F a).hem (!g) ∩ (F b).hem f = ∅ := by rw [Set.inter_comm]; exact h2
      have := (disjoint_unique (hF hab) h1 h2').1
      exact Bool.not_ne_self g this
    · simp only [Bool.not_not, Set.inter_self] at h3
      exact (F a).nonempty e |>.ne_empty h3
  comp_iff := by
    rintro ⟨a, e⟩ ⟨b, f⟩
    by_cases hab : a = b
    · subst hab
      simp only [Comp, famLt, famσ, ne_eq, not_true_eq_false, false_and, or_false,
        Prod.mk.injEq, true_and]
      cases e <;> cases f <;> simp
    · obtain ⟨e₀, f₀, h₀⟩ := (hF hab).2
      have hD : ∀ e' f', (F a).hem e' ∩ (F b).hem f' = ∅ ↔ e' = e₀ ∧ f' = f₀ := by
        intro e' f'
        constructor
        · exact fun h => disjoint_unique (hF hab) h₀ h
        · rintro ⟨rfl, rfl⟩; exact h₀
      have hD' : ∀ f' e', (F b).hem f' ∩ (F a).hem e' = ∅ ↔ e' = e₀ ∧ f' = f₀ := by
        intro f' e'; rw [Set.inter_comm]; exact hD e' f'
      have hba : b ≠ a := Ne.symm hab
      simp only [Comp, famLt, famσ, Prod.mk.injEq, hab, hba, ne_eq, not_false_eq_true,
        true_and, false_and, false_or, hD, hD']
      cases e <;> cases f <;> cases e₀ <;> cases f₀ <;> simp
  rev := by
    rintro ⟨a, e⟩ ⟨b, f⟩ ⟨hab, h⟩
    refine ⟨fun h' => hab h'.symm, ?_⟩
    simp only [famσ, Bool.not_not]
    rw [Set.inter_comm]; exact h

end Decomp

/-! ## The three chords around a triangle, as a non-parallel family -/

/-- The seven-point model of the disc cut by three chords around a triangle: `0` the open
triangle, `1, 2, 3` the chords `E₁, E₂, E₃`, `4, 5, 6` the open caps `K₁, K₂, K₃`. The cap
hemisphere of chord `i` is `{Kᵢ, Eᵢ}`, the other one is everything but `Kᵢ`. -/
def chordMem (i : Fin 3) : Bool → Fin 7 → Bool
  | true, x => x.val == i.val + 4 || x.val == i.val + 1
  | false, x => x.val != i.val + 4

def chordHem (i : Fin 3) (e : Bool) : Set (Fin 7) := {x | chordMem i e x = true}

theorem chordHem_inter_eq_empty {i j : Fin 3} {e f : Bool} :
    chordHem i e ∩ chordHem j f = ∅ ↔ ∀ x, ¬ (chordMem i e x = true ∧ chordMem j f x = true) := by
  simp [Set.eq_empty_iff_forall_notMem, chordHem]

theorem chordHem_eq {i j : Fin 3} {e f : Bool} :
    chordHem i e = chordHem j f ↔ ∀ x, chordMem i e x = chordMem j f x := by
  simp only [Set.ext_iff, chordHem, Set.mem_ofPred_eq]
  constructor
  · intro h x; cases h1 : chordMem i e x <;> cases h2 : chordMem j f x <;> simp_all
  · intro h x; rw [h x]

/-- The binary decomposition cut by chord `i`. -/
def chordDecomp (i : Fin 3) : Decomp (Fin 7) where
  hem := chordHem i
  cover := by
    ext x; simp only [chordHem, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    revert x; revert i; decide
  nonempty e := by
    cases e
    · exact ⟨0, by simp [chordHem, chordMem]⟩
    · exact ⟨⟨i.val + 4, by omega⟩, by simp [chordHem, chordMem]⟩
  ne := by
    rw [Ne, chordHem_eq]; revert i; decide

theorem chords_nonParallel : Pairwise fun i j => NonParallel (chordDecomp i) (chordDecomp j) := by
  intro i j hij
  refine ⟨?_, true, true, chordHem_inter_eq_empty.2 ?_⟩
  · simp only [Same, chordDecomp, chordHem_eq]
    revert hij; revert i j; decide
  · revert hij; revert i j; decide

theorem chords_isQuartette :
    IsQuartette famσ (famLt chordDecomp) := isQuartette_family chordDecomp chords_nonParallel

/-- The counterexample to page 39 inside the family: the cap side `c₁ = (0, true)` is below the
large sides `c₂' = (1, false)` and `c₃' = (2, false)`, which are incomparable. -/
theorem chords_family_not_chain :
    famLt chordDecomp (0, true) (1, false) ∧ famLt chordDecomp (0, true) (2, false) ∧
      ¬ Comp (famLt chordDecomp) (1, false) (2, false) := by
  simp only [Comp, famLt, chordDecomp, chordHem_inter_eq_empty]
  decide

/-! ## Page 47: the family of segments is not recovered from its cores -/

/-- The segment of `i` consecutive vertices of the hexagon starting at `s`. -/
def seg (s : Fin 6) (i : ℕ) : Finset (Fin 6) :=
  (Finset.range i).image fun k : ℕ => s + ⟨k % 6, Nat.mod_lt _ (by decide)⟩

/-- Page 41: a segment is a non-empty proper set of consecutive vertices. -/
def IsSegment (T : Finset (Fin 6)) : Prop := ∃ s : Fin 6, ∃ i ∈ Finset.Ioo 0 6, T = seg s i

instance : DecidablePred IsSegment := fun T =>
  inferInstanceAs (Decidable (∃ s : Fin 6, ∃ i ∈ Finset.Ioo 0 6, T = seg s i))

/-- The endpoints of a proper segment: its vertices with a neighbour outside it. -/
def endpoints (T : Finset (Fin 6)) : Finset (Fin 6) := T.filter fun t => t - 1 ∉ T ∨ t + 1 ∉ T

/-- Conditions (σ₁)–(σ₃) of pages 45 and 46, on a family of segments. -/
def Admissible (Sg : Finset (Finset (Fin 6))) : Prop :=
  (∀ A ∈ Sg, IsSegment A) ∧
  (∀ A ∈ Sg, ∀ B ∈ Sg, (A ∩ B).Nonempty → A ⊆ B ∨ B ⊆ A) ∧
  (∀ A ∈ Sg, ∀ B ∈ Sg, A ⊂ B → Disjoint A (endpoints B)) ∧
  ¬ IsSegment (Finset.univ \ Sg.sup id)

/-- Assembled conjunct by conjunct: under the full Mathlib import, instance search does not find
the decidability of the whole conjunction at once. -/
instance (Sg : Finset (Finset (Fin 6))) : Decidable (Admissible Sg) :=
  @instDecidableAnd _ _ (inferInstanceAs (Decidable (∀ A ∈ Sg, IsSegment A)))
    (@instDecidableAnd _ _
      (inferInstanceAs (Decidable (∀ A ∈ Sg, ∀ B ∈ Sg, (A ∩ B).Nonempty → A ⊆ B ∨ B ⊆ A)))
      (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (∀ A ∈ Sg, ∀ B ∈ Sg, A ⊂ B → Disjoint A (endpoints B))))
        (inferInstanceAs (Decidable (¬ IsSegment (Finset.univ \ Sg.sup id))))))

/-- The core `A* = A ∖ ⋃_{B ⊊ A} B` (page 45). -/
def core (Sg : Finset (Finset (Fin 6))) (A : Finset (Fin 6)) : Finset (Fin 6) :=
  A \ (Sg.filter (· ⊂ A)).sup id

/-- The hexagon `a₁, b, a₂, a₂', b', a₁'` is `0, 1, 2, 3, 4, 5`; three parallel chords
`a₁a₁' = {0, 5}`, `bb' = {1, 4}`, `a₂a₂' = {2, 3}`. -/
def sigma₁ : Finset (Finset (Fin 6)) := {{0, 5}, {2, 3}, {0, 1, 4, 5}}

def sigma₂ : Finset (Finset (Fin 6)) := {{0, 5}, {2, 3}, {1, 2, 3, 4}}

def R₀ : Finset (Finset (Fin 6)) := {{0, 5}, {1, 4}, {2, 3}}

/-- The NB of page 47: two distinct admissible families, both covering the hexagon (`Z = ∅`),
with the same partition into cores. -/
theorem page47_cores :
    Admissible sigma₁ ∧ Admissible sigma₂ ∧ sigma₁ ≠ sigma₂ ∧ sigma₁.sup id = Finset.univ ∧
      sigma₂.sup id = Finset.univ ∧ sigma₁.image (core sigma₁) = R₀ ∧
      sigma₂.image (core sigma₂) = R₀ := by
  decide

end Grothendieck.Folder81
