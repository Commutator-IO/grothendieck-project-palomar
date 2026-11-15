module

public import Mathlib
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Basic
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Tactic.Order
public import Mathlib.Data.Fintype.Powerset

@[expose] public section


/-!
# Folder 156-7, pages 61–98: supports by points, the two-strand string, and the orthomodular law

The modernised reading `transcripts/156-7/156-7.modern.tex` (chapter VII of *Vers une géométrie
des formes*, « Analysis situs (troisième mouture) », 23–26 June 1986) takes up the supports of
the first mouture (folder 156-4, pp. 65–68). For a symmetric relation `∥` (disjointness) on the
multistrates `𝓜`, the cosupport of `A ⊂ 𝓜` is the set of elements disjoint from every element
of `A`, the support is the cosupport of the cosupport, and a *support* is a part equal to its
support (pp. 61–63). Three passages are formalised.

* **Page 80, Proposition.** A map `X ↦ |X| : 𝓜 → 𝔓(P)` with
  `Supp¹_P : X ∥ Y ↔ |X| ∩ |Y| = ∅` and `Supp²_P : every point is some |X|`. With
  `|A| = ⋃_{X ∈ A} |X|`: `img_cosupp` (`|cosupp A| = P ∖ |A|`), `img_supp` (`|supp A| = |A|`),
  `subset_supp_iff` (`A ⊂ supp B ↔ |A| ⊂ |B|`), `supp_subset_supp_iff`, `orth_iff`
  (`A ∥ B ↔ |A| ∩ |B| = ∅`, from `Supp¹_P` alone), and `supportsIso`: `A ↦ |A|` is an order
  isomorphism from the supports onto `𝔓(P)`, `supportsIso_cosupp`: it carries the cosupport to
  the complement; the supports are therefore a complete atomic Boolean algebra.
* **Pages 81–83, the « ficelle à deux brins ».** Lieux `J = I × I'`, `I`, `I'` linear orders
  without least element (the open strands `]0, 1[`), two lieux disjoint when they are nested,
  `z < z'` or `z' < z` in the product order, and `|(x, x')| = {x, x'} ⊂ I ⊕ I'`.
  `ficelle_supp_singleton`: every `{z}` is a support (`ficelle_finite_not_supp`: not so without
  the hypothesis, already for two three-element chains). For `z₁ = (x₁, x'₁)`, `z₂ = (x₂, x'₂)`
  crossing (`x₁ < x₂`, `x'₂ < x'₁`) and `z₃` strictly between them on both strands:
  `ficelle_mem_supp` (`z₃ ∈ supp {z₁, z₂}`), `ficelle_not_distrib`
  (`{z₃} ∧ ({z₁} ∨ {z₂}) = {z₃}` while `({z₃} ∧ {z₁}) ∨ ({z₃} ∧ {z₂}) = ∅`),
  `ficelle_not_supp1` (`|z₁| ∩ |z₂| = ∅` though `z₁`, `z₂` are not disjoint) and
  `ficelle_img_ssubset` (`|A| ⊊ |supp A|` for `A = {z₁, z₂}`).
* **Page 98, « Rideau… ».** The Lemme 3 of page 97, `S ∥ S' ⇒ S' = (S ∨ S') ∩ ∁ S`, is the
  orthomodular law. `path_lemma3_false`: on the path `A' — A — B — B'` (disjoint = adjacent),
  `{A}` and `{B}` are disjoint supports, `{A} ∨ {B} = 𝓜`, and `(S ∨ S') ∩ ∁ S = {A', B} ≠ {B}`.
  `path_supports`: the supports are `∅, {A}, {B}, {A', B}, {A, B'}, 𝓜`.

**What the formalisation finds.** The Proposition of page 80 holds as stated, for any relation
whatever (symmetry follows from `Supp¹_P`); the surjectivity onto `𝔓(P)`, which the page does
not write, comes from `Supp²_P`. The two-strand string needs no density and no extremities: it
suffices that the strands have no least element, and then each `{z}` is a support. The graph of
page 98 is the disjointness graph of the edition's seven-element model of folder 156-4
(`Grothendieck.Folder156_4.Hexagon`), and its supports form the same hexagon: the lattice that
refuted the presumption of a Boolean algebra in the first mouture is the one by which the third
mouture refutes its own Lemme 3, which is the stronger failure — the lattice is not even
orthomodular.
-/

namespace Grothendieck.Folder156_7

section Polarity

variable {M : Type*} (r : M → M → Prop)

/-- The cosupport of `A`: the elements disjoint from every element of `A`. -/
def cosupp (A : Set M) : Set M := {X | ∀ Y ∈ A, r X Y}

/-- The support, cosupport of the cosupport. -/
def supp (A : Set M) : Set M := cosupp r (cosupp r A)

/-- A support is a part equal to its support. -/
def IsSupp (A : Set M) : Prop := supp r A = A

end Polarity

section Points

variable {M P : Type*} {r : M → M → Prop} {f : M → Set P}

/-- `|A| = ⋃_{X ∈ A} |X|`. -/
def img (f : M → Set P) (A : Set M) : Set P := ⋃ X ∈ A, f X

theorem mem_img {A : Set M} {p : P} : p ∈ img f A ↔ ∃ X ∈ A, p ∈ f X := by
  simp [img]

/-- Under `Supp¹_P`, `X ∈ cosupp A` iff `|X|` misses `|A|`. -/
theorem mem_cosupp_iff (h1 : ∀ X Y, r X Y ↔ f X ∩ f Y = ∅) {A : Set M} {X : M} :
    X ∈ cosupp r A ↔ f X ∩ img f A = ∅ := by
  simp only [cosupp, Set.mem_ofPred_eq, h1, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff,
    mem_img]
  constructor
  · rintro h p ⟨hp, Y, hY, hpY⟩
    exact h Y hY p ⟨hp, hpY⟩
  · rintro h Y hY p ⟨hp, hpY⟩
    exact h p ⟨hp, Y, hY, hpY⟩

/-- Page 80, (ii) 2°: `A ∥ B ↔ |A| ∩ |B| = ∅`, from `Supp¹_P` alone. -/
theorem orth_iff (h1 : ∀ X Y, r X Y ↔ f X ∩ f Y = ∅) {A B : Set M} :
    A ⊆ cosupp r B ↔ img f A ∩ img f B = ∅ := by
  simp only [Set.subset_def, mem_cosupp_iff h1, Set.eq_empty_iff_forall_notMem,
    Set.mem_inter_iff, mem_img]
  constructor
  · rintro h p ⟨⟨X, hX, hpX⟩, hpB⟩
    exact h X hX p ⟨hpX, hpB⟩
  · rintro h X hX p ⟨hpX, hpB⟩
    exact h p ⟨⟨X, hX, hpX⟩, hpB⟩

variable (h1 : ∀ X Y, r X Y ↔ f X ∩ f Y = ∅) (h2 : ∀ p : P, ∃ X, f X = {p})
include h1 h2

/-- Page 80: `|cosupp A| = P ∖ |A|`. -/
theorem img_cosupp (A : Set M) : img f (cosupp r A) = (img f A)ᶜ := by
  ext p
  constructor
  · intro hp hpA
    obtain ⟨X, hX, hpX⟩ := mem_img.1 hp
    exact ((mem_cosupp_iff h1).1 hX).subset ⟨hpX, hpA⟩
  · intro hp
    obtain ⟨X, hX⟩ := h2 p
    refine mem_img.2 ⟨X, (mem_cosupp_iff h1).2 ?_, by simp [hX]⟩
    rw [hX, Set.singleton_inter_eq_empty]
    exact hp

/-- Page 80: the support of `A` is the set of `X` with `|X| ⊂ |A|`. -/
theorem supp_eq (A : Set M) : supp r A = {X | f X ⊆ img f A} := by
  ext X
  rw [supp, mem_cosupp_iff h1, img_cosupp h1 h2, Set.mem_ofPred_eq]
  simp only [Set.eq_empty_iff_forall_notMem, Set.subset_def, Set.mem_inter_iff,
    Set.mem_compl_iff, not_and, not_not]

/-- Page 80, (i): `|supp A| = |A|`. -/
theorem img_supp (A : Set M) : img f (supp r A) = img f A := by
  rw [supp, img_cosupp h1 h2, img_cosupp h1 h2, compl_compl]

/-- Page 80, (ii) 1°: `A ⊂ supp B ↔ |A| ⊂ |B|`. -/
theorem subset_supp_iff {A B : Set M} : A ⊆ supp r B ↔ img f A ⊆ img f B := by
  rw [supp_eq h1 h2]
  constructor
  · intro h p hp
    obtain ⟨X, hX, hpX⟩ := mem_img.1 hp
    exact h hX hpX
  · intro h X hX p hp
    exact h (mem_img.2 ⟨X, hX, hp⟩)

/-- Page 80, (ii) 1°: `supp A ⊂ supp B ↔ |A| ⊂ |B|`. -/
theorem supp_subset_supp_iff {A B : Set M} : supp r A ⊆ supp r B ↔ img f A ⊆ img f B := by
  rw [subset_supp_iff h1 h2, img_supp h1 h2]

/-- Page 80, (iii): `A ↦ |A|` is an order isomorphism from the supports onto `𝔓(P)`. -/
def supportsIso : {A : Set M // IsSupp r A} ≃o Set P where
  toFun A := img f A.1
  invFun T := ⟨{X | f X ⊆ T}, by
    have hT : img f {X | f X ⊆ T} = T := by
      ext p
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · obtain ⟨X, hX, hpX⟩ := mem_img.1 hp
        exact hX hpX
      · obtain ⟨X, hX⟩ := h2 p
        exact mem_img.2 ⟨X, by simp [hX, hp], by simp [hX]⟩
    show supp r _ = _
    rw [supp_eq h1 h2, hT]⟩
  left_inv A := by
    apply Subtype.ext
    show {X | f X ⊆ img f A.1} = A.1
    rw [← supp_eq h1 h2]
    exact A.2
  right_inv T := by
    ext p
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨X, hX, hpX⟩ := mem_img.1 hp
      exact hX hpX
    · obtain ⟨X, hX⟩ := h2 p
      exact mem_img.2 ⟨X, by simp [hX, hp], by simp [hX]⟩
  map_rel_iff' {A B} := by
    show img f A.1 ⊆ img f B.1 ↔ A.1 ⊆ B.1
    rw [← subset_supp_iff h1 h2, B.2]

/-- Page 80, (iii): the isomorphism carries the cosupport to the complement. -/
theorem supportsIso_cosupp (A : {A : Set M // IsSupp r A}) :
    supportsIso h1 h2 ⟨cosupp r A.1, by
      show cosupp r (supp r A.1) = cosupp r A.1
      rw [A.2]⟩ = (supportsIso h1 h2 A)ᶜ :=
  img_cosupp h1 h2 A.1

end Points

section Ficelle

variable {I I' : Type*} [LinearOrder I] [LinearOrder I'] [NoMinOrder I] [NoMinOrder I']

/-- Two lieux of the two-strand string are disjoint when they are nested. -/
def nested (z w : I × I') : Prop := z < w ∨ w < z

/-- The point support `|(x, x')| = {x, x'}` in `I ⊕ I'`. -/
def pt (z : I × I') : Set (I ⊕ I') := {Sum.inl z.1, Sum.inr z.2}

/-- Pages 82–83: every `{z}` is a support. -/
theorem ficelle_supp_singleton (z : I × I') : supp nested {z} = {z} := by
  ext w
  simp only [supp, cosupp, Set.mem_singleton_iff, forall_eq, Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun h u hu => ?_⟩
  · by_contra hne
    obtain ⟨c, d⟩ := z
    obtain ⟨c', hc'⟩ := exists_lt c
    obtain ⟨d', hd'⟩ := exists_lt d
    have k0 : ¬ nested w (c, d) := fun hn => (h _ hn).elim (lt_irrefl _) (lt_irrefl _)
    have n1 : ¬ w ≤ (c, d) := fun hle => k0 (Or.inl (lt_of_le_of_ne hle hne))
    have n2 : ¬ (c, d) ≤ w := fun hle => k0 (Or.inr (lt_of_le_of_ne hle (Ne.symm hne)))
    have hca : c ≤ w.1 := by
      rcases h (c, d') (Or.inl (Prod.lt_iff.2 (Or.inr ⟨le_rfl, hd'⟩))) with k | k
      · exact absurd (k.le.trans (Prod.mk_le_mk.2 ⟨le_rfl, hd'.le⟩)) n1
      · exact (Prod.mk_le_mk.1 k.le).1
    have hdb : d ≤ w.2 := by
      rcases h (c', d) (Or.inl (Prod.lt_iff.2 (Or.inl ⟨hc', le_rfl⟩))) with k | k
      · exact absurd (k.le.trans (Prod.mk_le_mk.2 ⟨hc'.le, le_rfl⟩)) n1
      · exact (Prod.mk_le_mk.1 k.le).2
    exact n2 ⟨hca, hdb⟩
  · rw [h]
    exact Or.symm hu

/-- Without `NoMinOrder` a singleton need not be a support: in the product of two three-element
chains, `(1, 1) ∈ supp {(0, 2)}`. -/
theorem ficelle_finite_not_supp :
    ((1, 1) : Fin 3 × Fin 3) ∈ supp nested {((0, 2) : Fin 3 × Fin 3)} := by
  simp only [supp, cosupp, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
  simp only [nested, Prod.lt_iff, Prod.forall]
  decide

variable {x₁ x₂ x₃ : I} {y₁ y₂ y₃ : I'}

omit [NoMinOrder I] [NoMinOrder I'] in
/-- Page 83: for crossing `z₁ = (x₁, y₁)`, `z₂ = (x₂, y₂)` and `z₃` strictly between them on
both strands, `z₃ ∈ supp {z₁, z₂}`. -/
theorem ficelle_mem_supp (h13 : x₁ < x₃) (h32 : x₃ < x₂) (h23 : y₂ < y₃) (h31 : y₃ < y₁) :
    (x₃, y₃) ∈ supp nested {(x₁, y₁), (x₂, y₂)} := by
  intro u hu
  have hu1 := hu (x₁, y₁) (by simp)
  have hu2 := hu (x₂, y₂) (by simp)
  obtain ⟨a, b⟩ := u
  simp only [nested, Prod.lt_iff] at hu1 hu2 ⊢
  rcases hu1 with ((⟨h1, h1'⟩ | ⟨h1, h1'⟩) | (⟨h1, h1'⟩ | ⟨h1, h1'⟩)) <;>
  rcases hu2 with ((⟨h2, h2'⟩ | ⟨h2, h2'⟩) | (⟨h2, h2'⟩ | ⟨h2, h2'⟩)) <;>
  first
  | (left; left; constructor <;> order)
  | (right; left; constructor <;> order)

omit [NoMinOrder I] [NoMinOrder I'] in
/-- Pages 82–83, **the supports of the two-strand string are not distributive**: with meet the
intersection and join the support of the union, `{z₃} ∧ ({z₁} ∨ {z₂}) = {z₃}` while
`({z₃} ∧ {z₁}) ∨ ({z₃} ∧ {z₂}) = ∅`. -/
theorem ficelle_not_distrib (h13 : x₁ < x₃) (h32 : x₃ < x₂) (h23 : y₂ < y₃) (h31 : y₃ < y₁) :
    ({(x₃, y₃)} : Set (I × I')) ∩ supp nested ({(x₁, y₁)} ∪ {(x₂, y₂)}) = {(x₃, y₃)} ∧
      supp nested (({(x₃, y₃)} : Set (I × I')) ∩ {(x₁, y₁)} ∪ {(x₃, y₃)} ∩ {(x₂, y₂)}) = ∅ := by
  constructor
  · rw [Set.inter_eq_left, Set.singleton_subset_iff, Set.singleton_union]
    exact ficelle_mem_supp h13 h32 h23 h31
  · have e1 : ({(x₃, y₃)} : Set (I × I')) ∩ {(x₁, y₁)} = ∅ :=
      Set.singleton_inter_eq_empty.2 (by simp [h13.ne'])
    have e2 : ({(x₃, y₃)} : Set (I × I')) ∩ {(x₂, y₂)} = ∅ :=
      Set.singleton_inter_eq_empty.2 (by simp [h32.ne])
    rw [e1, e2, Set.union_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun w hw => ?_
    rcases hw w (fun _ h => h.elim) with h | h <;> exact lt_irrefl _ h

omit [NoMinOrder I] [NoMinOrder I'] in
/-- Page 81: `Supp¹_P` fails for the point supports `|(x, x')| = {x, x'}`: crossing lieux have
disjoint point supports without being disjoint. -/
theorem ficelle_not_supp1 (h12 : x₁ < x₂) (h21 : y₂ < y₁) :
    pt (x₁, y₁) ∩ pt (x₂, y₂) = ∅ ∧ ¬ nested (x₁, y₁) (x₂, y₂) := by
  refine ⟨?_, ?_⟩
  · ext p
    simp only [pt, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (rfl | rfl) (h | h) <;> simp_all [h12.ne, h21.ne']
  · simp only [nested, Prod.lt_iff]
    rintro ((⟨h, h'⟩ | ⟨h, h'⟩) | (⟨h, h'⟩ | ⟨h, h'⟩)) <;> order

omit [NoMinOrder I] [NoMinOrder I'] in
/-- Page 83: `|A| ⊊ |supp A|` for `A = {z₁, z₂}`; the point `x₃` of the first strand lies in
`|supp A|` and not in `|A|`. -/
theorem ficelle_img_ssubset (h13 : x₁ < x₃) (h32 : x₃ < x₂) (h23 : y₂ < y₃) (h31 : y₃ < y₁) :
    img pt ({(x₁, y₁), (x₂, y₂)} : Set (I × I')) ⊂
      img pt (supp nested ({(x₁, y₁), (x₂, y₂)} : Set (I × I'))) := by
  refine Set.ssubset_iff_of_subset ?_ |>.2 ⟨Sum.inl x₃, ?_, ?_⟩
  · intro p hp
    obtain ⟨X, hX, hpX⟩ := mem_img.1 hp
    refine mem_img.2 ⟨X, ?_, hpX⟩
    intro u hu
    rcases hu X hX with h | h
    · exact Or.inr h
    · exact Or.inl h
  · exact mem_img.2 ⟨(x₃, y₃), ficelle_mem_supp h13 h32 h23 h31, by simp [pt]⟩
  · intro hp
    obtain ⟨X, hX, hpX⟩ := mem_img.1 hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl <;> simp only [pt, Set.mem_insert_iff, Set.mem_singleton_iff,
      Sum.inl.injEq, reduceCtorEq, or_false] at hpX <;> order

end Ficelle

section Path

/-- The path `A' — A — B — B'`: `0, 1, 2, 3` are `A', A, B, B'`. -/
def adj (x y : Fin 4) : Prop := x.val + 1 = y.val ∨ y.val + 1 = x.val

instance : DecidableRel adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The cosupport on the path. -/
def cosuppP (S : Finset (Fin 4)) : Finset (Fin 4) := Finset.univ.filter fun x => ∀ y ∈ S, adj x y

/-- The support on the path. -/
def suppP (S : Finset (Fin 4)) : Finset (Fin 4) := cosuppP (cosuppP S)

/-- The finite computation agrees with the general definition. -/
theorem coe_cosuppP (S : Finset (Fin 4)) : (cosuppP S : Set (Fin 4)) = cosupp adj S := by
  ext x
  simp [cosuppP, cosupp]

/-- Page 98: `cosupp A = {A', B}`, `supp A = {A}`, `cosupp B = {A, B'}`, `supp B = {B}`, and the
supports of the path are `∅, {A}, {B}, {A', B}, {A, B'}, 𝓜`. -/
theorem path_supports :
    cosuppP {1} = {0, 2} ∧ suppP {1} = {1} ∧ cosuppP {2} = {1, 3} ∧ suppP {2} = {2} ∧
      Finset.univ.filter (fun S : Finset (Fin 4) => suppP S = S) =
        {∅, {1}, {2}, {0, 2}, {1, 3}, Finset.univ} := by
  decide

/-- Page 98, **the Lemme 3 of page 97 is false**: `S = {A}` and `S' = {B}` are disjoint
supports, `S ∨ S' = 𝓜`, and `(S ∨ S') ∩ ∁ S = {A', B} ≠ S'`. The orthomodular law fails. -/
theorem path_lemma3_false :
    suppP {1} = {1} ∧ suppP {2} = {2} ∧ (∀ x ∈ ({1} : Finset (Fin 4)), ∀ y ∈ ({2} : Finset _),
      adj x y) ∧ suppP ({1} ∪ {2}) = Finset.univ ∧
      suppP ({1} ∪ {2}) ∩ cosuppP {1} = {0, 2} ∧ ({0, 2} : Finset (Fin 4)) ≠ {2} := by
  decide

end Path

end Grothendieck.Folder156_7
