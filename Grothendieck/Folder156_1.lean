module

public import Mathlib

@[expose] public section


/-!
# Folder 156-1, the segment model is a biorder (pages 10–13)

The modernised reading `transcripts/156-1/156-1.modern.tex` gives, for the third
draft of chapter I of *Vers une géométrie des formes* (pages 5–9), a model of a
one-dimensional form: a set `L` of lieux, a set `S` of segments, and for each
segment `I` its set of lieux `Ĩ` (here `car I`) and its two extremities `∂I`
(here `bd I`), with `∂I ⊆ Ĩ`. The axioms are F1 (divisibility), F2, F3
(branches), the filtering condition F′3 that the reading reconstructs from the
foot of page 6, F4 (gluing at a regular lieu) and F5 (a regular lieu has order
two). They are written below as the reading states them, with `I_{x,z}` the
sub-segment of `I` with extremities `x, z` given by F1, which here is a
hypothesis `IsSub I x z J` on a segment `J`.

The finding `156-1-segment-biorder` (`src/content/findings.ts`) states, after
pages 12–13, that a model which is a single segment is the same thing as a
poset with distinct least and greatest elements, dense and locally directed in
both directions, the segments being the intervals `[x, y]`, `x < y`, and that
the order need not be total. Proved here:

* `SegModel.biorder` — the forward direction: fixing an extremity `x₀` of the
  segment `I = L`, the relation of page 11, `x ≤ y` iff `x ∈ [x₀, y]`, is a
  partial order with least element `x₀` and greatest `x₁`, dense, locally
  directed downwards and upwards, whose intervals `[x, y]`, `x < y`, are
  exactly the segments, each carried by exactly one segment;
* `SegModel.le_swap` — exchanging the extremities replaces the order by its
  opposite (page 13: the structure is a biorder);
* `intervals_axioms`, `intervals_segModel`, `intervals_le_iff` — the converse:
  on a bounded poset with `⊥ ≠ ⊤`, dense and locally directed both ways, the
  intervals satisfy F1–F5 and F′3, the whole set is a segment, and the order
  read back from it at `⊥` is the given one;
* `Diamond.example_segModel` — a poset of this kind that is not totally
  ordered (the points between `(0, 0)` and `(2, 0)` for the open-cone order on
  `ℚ²`), hence a model-segment whose order is not total.

What the proof makes plain. The forward direction uses F1, F2, F′3 and F4 only:
F3 and F5 are not needed for it. F′3 gives local directedness and nothing else
does: F4, at a regular lieu, is what makes every interval a segment. In the
converse F4 holds without its regularity hypothesis, and of the bounds only
`⊥ ≠ ⊤` and `Icc ⊥ ⊤ = univ` are used, for the whole set to be a segment.
What this certifies is that the reading holds together, not that it is what the
page says (issue #26), and not that the statement is new: the finding stays
open as a literature question.
-/

namespace Grothendieck.Folder156_1

open Set

/-- The data of a model of a one-dimensional form (page 5): for each segment
its set of lieux `car I = Ĩ` and its extremities `bd I = ∂I`. -/
structure Data (L S : Type*) where
  /-- the lieux on a segment, `Ĩ` -/
  car : S → Set L
  /-- the extremities of a segment, `∂I` -/
  bd : S → Set L

namespace Data

variable {L S : Type*} (M : Data L S)

/-- The interior lieux `I° = Ĩ ∖ ∂I`. -/
def intr (I : S) : Set L := M.car I \ M.bd I

/-- `J` is the sub-segment `I_{x,z}` of `I`: `J̃ ⊆ Ĩ` and `∂J = {x, z}` (F1). -/
def IsSub (I : S) (x z : L) (J : S) : Prop := M.car J ⊆ M.car I ∧ M.bd J = {x, z}

/-- A regular lieu is interior to some segment (page 7). -/
def Regular (x : L) : Prop := ∃ I, x ∈ M.intr I

/-- `I R_x J`: the segments `I, J` issued from `x` define the same branch at `x`
(page 6): some `z ∈ I° ∩ J°` has `I_{x,z} = J_{x,z}`. -/
def SameBranch (x : L) (I J : S) : Prop :=
  x ∈ M.bd I ∧ x ∈ M.bd J ∧ ∃ z ∈ M.intr I ∩ M.intr J, ∃ K, M.IsSub I x z K ∧ M.IsSub J x z K

/-- The lieu `x` has order two: two segments issued from `x` in different
branches, and every segment issued from `x` in the branch of one of them. -/
def OrderTwo (x : L) : Prop :=
  ∃ I J, x ∈ M.bd I ∧ x ∈ M.bd J ∧ ¬ M.SameBranch x I J ∧
    ∀ K, x ∈ M.bd K → M.SameBranch x K I ∨ M.SameBranch x K J

/-- The axioms F1–F5 and F′3 of the third draft (pages 5–8), as the reading
states them. -/
structure Axioms : Prop where
  /-- `∂I` is a two-element set. -/
  bd_pair : ∀ I, ∃ x y, x ≠ y ∧ M.bd I = {x, y}
  /-- `∂I ⊆ Ĩ`. -/
  bd_sub : ∀ I, M.bd I ⊆ M.car I
  /-- **F1**: for `x ∈ ∂I` and `z ∈ Ĩ ∖ {x}`, there is a unique `I_{x,z}`. -/
  F1 : ∀ I x, x ∈ M.bd I → ∀ z ∈ M.car I, z ≠ x → ∃! J, M.IsSub I x z J
  /-- **F2**, first clause: `I° ≠ ∅`. -/
  F2_intr : ∀ I, (M.intr I).Nonempty
  /-- **F2**: for `∂I = {x, y}` and `z ∈ I°`, `Ĩ_{x,z} ∩ Ĩ_{y,z} = {z}`, and every
  sub-segment of `I` with extremity `z` lies in `I_{x,z}` or in `I_{y,z}`. -/
  F2 : ∀ I x y z, M.bd I = {x, y} → z ∈ M.intr I → ∀ Jx Jy, M.IsSub I x z Jx →
    M.IsSub I y z Jy → M.car Jx ∩ M.car Jy = {z} ∧
      ∀ J, M.car J ⊆ M.car I → z ∈ M.bd J → M.car J ⊆ M.car Jx ∨ M.car J ⊆ M.car Jy
  /-- **F3** (branches), in the margin's form `u ∈ I ∖ {x}`, `v ∈ J ∖ {x}`. -/
  F3 : ∀ I J x, x ∈ M.bd I → x ∈ M.bd J → ∃ u ∈ M.car I, u ≠ x ∧ ∃ v ∈ M.car J, v ≠ x ∧
    ∃ Iu Jv, M.IsSub I x u Iu ∧ M.IsSub J x v Jv ∧ (Iu = Jv ∨ M.car Iu ∩ M.car Jv = {x})
  /-- **F′3** (filtering at an extremity), the reading's reconstruction. -/
  F3' : ∀ I x, x ∈ M.bd I → ∀ u ∈ M.intr I, ∀ v ∈ M.intr I, ∃ w ∈ M.intr I,
    ∀ Iu Iv Iw, M.IsSub I x u Iu → M.IsSub I x v Iv → M.IsSub I x w Iw →
      M.car Iw ⊆ M.car Iu ∩ M.car Iv
  /-- **F4** (gluing at a regular lieu). -/
  F4 : ∀ I' I'' x y z, M.Regular z → M.car I' ∩ M.car I'' = {z} → M.bd I' = {x, z} →
    M.bd I'' = {y, z} → ∃! I, M.car I' ∪ M.car I'' ⊆ M.car I ∧ M.bd I = {x, y}
  /-- **F5**: a regular lieu has order two. -/
  F5 : ∀ x, M.Regular x → M.OrderTwo x

/-- The relation of page 11 from the extremity `x₀`: `a ≤ b` iff `a ∈ [x₀, b]`,
where `[x₀, x₀] = {x₀}` and `[x₀, b] = Ĩ_{x₀,b}` otherwise. -/
def le (x0 : L) (a b : L) : Prop := a = b ∨ ∃ J, M.bd J = {x0, b} ∧ a ∈ M.car J

/-- The strict relation. -/
def lt (x0 : L) (a b : L) : Prop := M.le x0 a b ∧ a ≠ b

/-- A model which is a single segment `I = L` (page 10), with `∂I = {x₀, x₁}`. -/
structure SegModel (I : S) (x0 x1 : L) : Prop where
  ax : M.Axioms
  car_eq : M.car I = univ
  bd_eq : M.bd I = {x0, x1}

variable {M}

theorem le_refl' (x0 a : L) : M.le x0 a a := Or.inl rfl

namespace Axioms

variable (hM : M.Axioms)
include hM

theorem ne_of_bd {J : S} {a b : L} (h : M.bd J = {a, b}) : a ≠ b := by
  rintro rfl
  obtain ⟨x, y, hxy, hJ⟩ := hM.bd_pair J
  rcases pair_eq_pair_iff.1 (hJ.symm.trans h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hxy rfl

theorem left_mem {J : S} {a b : L} (h : M.bd J = {a, b}) : a ∈ M.car J :=
  hM.bd_sub J (by rw [h]; simp)

theorem right_mem {J : S} {a b : L} (h : M.bd J = {a, b}) : b ∈ M.car J :=
  hM.bd_sub J (by rw [h]; simp)

/-- The uniqueness clause of F1. -/
theorem sub_unique {P J J' : S} {x z : L} (hx : x ∈ M.bd P) (hz : z ∈ M.car P) (hzx : z ≠ x)
    (hJ : M.IsSub P x z J) (hJ' : M.IsSub P x z J') : J = J' :=
  (hM.F1 P x hx z hz hzx).unique hJ hJ'

end Axioms

namespace SegModel

variable {I : S} {x0 x1 : L} (h : M.SegModel I x0 x1)
include h

theorem x0_bd : x0 ∈ M.bd I := by rw [h.bd_eq]; simp

theorem x1_bd : x1 ∈ M.bd I := by rw [h.bd_eq]; simp

theorem mem_car (a : L) : a ∈ M.car I := h.car_eq ▸ mem_univ a

theorem isSub {J : S} {e w : L} (hJ : M.bd J = {e, w}) : M.IsSub I e w J :=
  ⟨h.car_eq ▸ subset_univ _, hJ⟩

theorem mem_intr {a : L} (h0 : a ≠ x0) (h1 : a ≠ x1) : a ∈ M.intr I :=
  ⟨h.mem_car a, by rw [h.bd_eq]; simp [h0, h1]⟩

theorem exists_x0 {b : L} (hb : b ≠ x0) : ∃ J, M.bd J = {x0, b} := by
  obtain ⟨J, hJ, -⟩ := h.ax.F1 I x0 h.x0_bd b (h.mem_car b) hb
  exact ⟨J, hJ.2⟩

theorem uniq0 {J J' : S} {b : L} (hJ : M.bd J = {x0, b}) (hJ' : M.bd J' = {x0, b}) :
    J = J' :=
  h.ax.sub_unique h.x0_bd (h.mem_car b) (h.ax.ne_of_bd hJ).symm (h.isSub hJ) (h.isSub hJ')

theorem le_iff {J : S} {a b : L} (hJ : M.bd J = {x0, b}) : M.le x0 a b ↔ a ∈ M.car J :=
  ⟨fun hab => hab.elim (· ▸ h.ax.right_mem hJ) fun ⟨_, hJ', ha⟩ => h.uniq0 hJ hJ' ▸ ha,
    fun ha => Or.inr ⟨J, hJ, ha⟩⟩

theorem le_x0 {a : L} : M.le x0 a x0 ↔ a = x0 :=
  ⟨fun ha => ha.elim id fun ⟨_, hJ, _⟩ => absurd rfl (h.ax.ne_of_bd hJ), Or.inl⟩

theorem bot_le (a : L) : M.le x0 x0 a := by
  by_cases ha : a = x0
  · exact Or.inl ha.symm
  · obtain ⟨J, hJ⟩ := h.exists_x0 ha
    exact Or.inr ⟨J, hJ, h.ax.left_mem hJ⟩

theorem le_top (a : L) : M.le x0 a x1 := Or.inr ⟨I, h.bd_eq, h.mem_car a⟩

/-- `[x₀, b] ⊆ [x₀, c]` as soon as `b ∈ [x₀, c]`. -/
theorem car_sub {Jb Jc : S} {b c : L} (hb : M.bd Jb = {x0, b}) (hc : M.bd Jc = {x0, c})
    (hbc : b ∈ M.car Jc) : M.car Jb ⊆ M.car Jc := by
  obtain ⟨K, hK, -⟩ := h.ax.F1 Jc x0 (by rw [hc]; simp) b hbc (h.ax.ne_of_bd hb).symm
  rw [h.uniq0 hb hK.2]; exact hK.1

theorem le_trans' {a b c : L} (hab : M.le x0 a b) (hbc : M.le x0 b c) : M.le x0 a c := by
  rcases hab with rfl | ⟨Jb, hb, ha⟩
  · exact hbc
  rcases hbc with rfl | ⟨Jc, hc, hb'⟩
  · exact Or.inr ⟨Jb, hb, ha⟩
  exact Or.inr ⟨Jc, hc, h.car_sub hb hc hb' ha⟩

theorem le_antisymm' {a b : L} (hab : M.le x0 a b) (hba : M.le x0 b a) : a = b := by
  by_contra hne
  rcases hab with rfl | ⟨Jb, hb, ha⟩
  · exact hne rfl
  rcases hba with hba | ⟨Ja, hJa, hb'⟩
  · exact hne hba.symm
  have ha0 : a ≠ x0 := fun e => by rw [e] at hJa; exact h.ax.ne_of_bd hJa rfl
  have hJab : M.car Ja ⊆ M.car Jb := h.car_sub hJa hb ha
  have hJba : M.car Jb ⊆ M.car Ja := h.car_sub hb hJa hb'
  obtain ⟨K, hK, -⟩ := h.ax.F1 Jb b (by rw [hb]; simp) a ha hne
  have haint : a ∈ M.intr Jb := ⟨ha, by rw [hb]; simp [ha0, hne]⟩
  have h2 := (h.ax.F2 Jb x0 b a hb haint Ja K ⟨hJab, hJa⟩ hK).1
  exact hne (h2.subset ⟨hJba (h.ax.right_mem hb), h.ax.left_mem hK.2⟩).symm

/-- Two segments of the segment model with the same extremities are equal
(corollary 3 a of page 5, in the segment model). -/
theorem bd_inj {J K : S} (hJK : M.bd J = M.bd K) : J = K := by
  obtain ⟨u, v, huv, hJ⟩ := h.ax.bd_pair J
  have hK : M.bd K = {u, v} := by rw [← hJK]; exact hJ
  by_cases hu : u ∈ M.bd I
  · exact h.ax.sub_unique hu (h.mem_car v) huv.symm (h.isSub hJ) (h.isSub hK)
  by_cases hv : v ∈ M.bd I
  · rw [pair_comm u v] at hJ hK
    exact h.ax.sub_unique hv (h.mem_car u) huv (h.isSub hJ) (h.isSub hK)
  have hu0 : u ≠ x0 := fun e => hu (e ▸ h.x0_bd)
  have hu1 : u ≠ x1 := fun e => hu (e ▸ h.x1_bd)
  obtain ⟨Ju, hJu, -⟩ := h.ax.F1 I x0 h.x0_bd u (h.mem_car u) hu0
  obtain ⟨Pu, hPu, -⟩ := h.ax.F1 I x1 h.x1_bd u (h.mem_car u) hu1
  have hF2 := h.ax.F2 I x0 x1 u h.bd_eq (h.mem_intr hu0 hu1) Ju Pu hJu hPu
  have hvJ : v ∈ M.car J := h.ax.right_mem hJ
  have hvK : v ∈ M.car K := h.ax.right_mem hK
  have key : ∀ Q, u ∈ M.bd Q → M.car J ⊆ M.car Q → M.car K ⊆ M.car Q → J = K :=
    fun Q hQ hJQ hKQ => h.ax.sub_unique hQ (hJQ hvJ) huv.symm ⟨hJQ, hJ⟩ ⟨hKQ, hK⟩
  rcases hF2.2 J (h.isSub hJ).1 (by rw [hJ]; simp) with hJ1 | hJ1 <;>
    rcases hF2.2 K (h.isSub hK).1 (by rw [hK]; simp) with hK1 | hK1
  · exact key Ju (by rw [hJu.2]; simp) hJ1 hK1
  · exact absurd (hF2.1.subset ⟨hJ1 hvJ, hK1 hvK⟩) huv.symm
  · exact absurd (hF2.1.subset ⟨hK1 hvK, hJ1 hvJ⟩) huv.symm
  · exact key Pu (by rw [hPu.2]; simp) hJ1 hK1

/-- Gluing (F4) at a regular lieu `a`: if `[x₀, a]` meets a segment `Q` with
extremities `a, z` only in `a`, then `a ≤ z`. -/
theorem glue {a z : L} {Ja Q : S} (ha : M.Regular a) (hJa : M.bd Ja = {x0, a})
    (hQ : M.bd Q = {a, z}) (hint : M.car Ja ∩ M.car Q = {a}) : M.le x0 a z := by
  obtain ⟨G, ⟨hG, hGbd⟩, -⟩ := h.ax.F4 Ja Q x0 z a ha hint hJa (by rw [hQ, pair_comm])
  exact Or.inr ⟨G, hGbd, hG (mem_union_left _ (h.ax.right_mem hJa))⟩

theorem inter_eq {a z : L} {Ja K Q : S} (hJa : M.bd Ja = {x0, a}) (hQ : M.bd Q = {a, z})
    (hQK : M.car Q ⊆ M.car K) (hint : M.car Ja ∩ M.car K = {a}) :
    M.car Ja ∩ M.car Q = {a} := by
  apply Subset.antisymm
  · rw [← hint]; exact inter_subset_inter_right _ hQK
  · rw [singleton_subset_iff]; exact ⟨h.ax.right_mem hJa, h.ax.left_mem hQ⟩

/-- The extremities of a segment are comparable. -/
theorem lt_or_lt_of_bd {J : S} {u v : L} (hJ : M.bd J = {u, v}) :
    M.lt x0 u v ∨ M.lt x0 v u := by
  have huv := h.ax.ne_of_bd hJ
  obtain rfl | hu0 := eq_or_ne u x0
  · exact Or.inl ⟨h.bot_le v, huv⟩
  obtain rfl | hv0 := eq_or_ne v x0
  · exact Or.inr ⟨h.bot_le u, huv.symm⟩
  obtain rfl | hu1 := eq_or_ne u x1
  · exact Or.inr ⟨h.le_top v, huv.symm⟩
  obtain rfl | hv1 := eq_or_ne v x1
  · exact Or.inl ⟨h.le_top u, huv⟩
  have hu := h.mem_intr hu0 hu1
  obtain ⟨Ju, hJu, -⟩ := h.ax.F1 I x0 h.x0_bd u (h.mem_car u) hu0
  obtain ⟨Pu, hPu, -⟩ := h.ax.F1 I x1 h.x1_bd u (h.mem_car u) hu1
  have hF2 := h.ax.F2 I x0 x1 u h.bd_eq hu Ju Pu hJu hPu
  have hvJ : v ∈ M.car J := h.ax.right_mem hJ
  rcases hF2.2 J (h.isSub hJ).1 (by rw [hJ]; simp) with h1 | h1
  · exact Or.inr ⟨(h.le_iff hJu.2).2 (h1 hvJ), huv.symm⟩
  · obtain ⟨Q, hQ, -⟩ := h.ax.F1 Pu u (by rw [hPu.2]; simp) v (h1 hvJ) huv.symm
    exact Or.inl ⟨h.glue ⟨I, hu⟩ hJu.2 hQ.2 (h.inter_eq hJu.2 hQ.2 hQ.1 hF2.1), huv⟩

theorem ne_x0_of_lt {a b : L} (hab : M.lt x0 a b) : b ≠ x0 := fun e => by
  rw [e] at hab; exact hab.2 (h.le_x0.1 hab.1)

theorem ne_x1_of_lt {a b : L} (hab : M.lt x0 a b) : a ≠ x1 := fun e => by
  rw [e] at hab; exact hab.2 (h.le_antisymm' hab.1 (h.le_top b))

/-- A segment with extremities `a < b` has for lieux the interval `[a, b]`
(page 12). -/
theorem car_eq_Icc {K : S} {a b : L} (hab : M.lt x0 a b) (hK : M.bd K = {a, b}) :
    M.car K = {z | M.le x0 a z ∧ M.le x0 z b} := by
  obtain ⟨Jb, hJb⟩ := h.exists_x0 (h.ne_x0_of_lt hab)
  by_cases ha0 : a = x0
  · rw [ha0] at hK ⊢
    ext z
    exact ⟨fun hz => ⟨h.bot_le z, (h.le_iff hK).2 hz⟩, fun hz => (h.le_iff hK).1 hz.2⟩
  have haJb : a ∈ M.car Jb := (h.le_iff hJb).1 hab.1
  obtain ⟨K', hK', -⟩ := h.ax.F1 Jb b (by rw [hJb]; simp) a haJb hab.2
  obtain rfl : K' = K := h.bd_inj (by rw [hK'.2, hK, pair_comm])
  obtain ⟨Ja, hJa⟩ := h.exists_x0 ha0
  have hJaJb : M.car Ja ⊆ M.car Jb := h.car_sub hJa hJb haJb
  have haint : a ∈ M.intr Jb := ⟨haJb, by rw [hJb]; simp [ha0, hab.2]⟩
  have hF2 := h.ax.F2 Jb x0 b a hJb haint Ja K' ⟨hJaJb, hJa⟩ hK'
  have hreg : M.Regular a := ⟨I, h.mem_intr ha0 (h.ne_x1_of_lt hab)⟩
  ext z
  constructor
  · intro hz
    refine ⟨?_, (h.le_iff hJb).2 (hK'.1 hz)⟩
    by_cases hza : z = a
    · rw [hza]; exact le_refl' x0 a
    obtain ⟨Q, hQ, -⟩ := h.ax.F1 K' a (by rw [hK'.2]; simp) z hz hza
    exact h.glue hreg hJa hQ.2 (h.inter_eq hJa hQ.2 hQ.1 hF2.1)
  · rintro ⟨haz, hzb⟩
    by_cases hza : z = a
    · rw [hza]; exact h.ax.right_mem hK'.2
    have hz0 : z ≠ x0 := fun e => by rw [e] at haz; exact ha0 (h.le_x0.1 haz)
    obtain ⟨Jz, hJz⟩ := h.exists_x0 hz0
    have hJzJb := h.car_sub hJz hJb ((h.le_iff hJb).1 hzb)
    obtain ⟨Q, hQ, -⟩ := h.ax.F1 Jz z (by rw [hJz]; simp) a ((h.le_iff hJz).1 haz)
      (Ne.symm hza)
    rcases hF2.2 Q (hQ.1.trans hJzJb) (by rw [hQ.2]; simp) with hQa | hQK
    · exact absurd (h.le_antisymm' ((h.le_iff hJa).2 (hQa (h.ax.left_mem hQ.2))) haz) hza
    · exact hQK (h.ax.left_mem hQ.2)

theorem exists_seg {a b : L} (hab : M.lt x0 a b) : ∃ K, M.bd K = {a, b} := by
  obtain ⟨Jb, hJb⟩ := h.exists_x0 (h.ne_x0_of_lt hab)
  obtain ⟨K, hK, -⟩ := h.ax.F1 Jb b (by rw [hJb]; simp) a ((h.le_iff hJb).1 hab.1) hab.2
  exact ⟨K, by rw [hK.2, pair_comm]⟩

/-- Property a) of page 12: the order is dense (« infiniment divisible »). -/
theorem dense {a b : L} (hab : M.lt x0 a b) : ∃ c, M.lt x0 a c ∧ M.lt x0 c b := by
  obtain ⟨K, hK⟩ := h.exists_seg hab
  obtain ⟨c, hc, hcb⟩ := h.ax.F2_intr K
  rw [h.car_eq_Icc hab hK] at hc
  rw [hK] at hcb
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hcb
  exact ⟨c, ⟨hc.1, Ne.symm hcb.1⟩, ⟨hc.2, hcb.2⟩⟩

/-- Property b) of page 12: locally directed downwards, from F′3 at the
extremity `a` of `[a, x₁]`. -/
theorem dir_down {a y₁ y₂ : L} (h₁ : M.lt x0 a y₁) (h₂ : M.lt x0 a y₂) :
    ∃ y, M.lt x0 a y ∧ M.le x0 y y₁ ∧ M.le x0 y y₂ := by
  by_cases e₁ : y₁ = x1
  · exact ⟨y₂, h₂, e₁ ▸ h.le_top y₂, le_refl' x0 y₂⟩
  by_cases e₂ : y₂ = x1
  · exact ⟨y₁, h₁, le_refl' x0 y₁, e₂ ▸ h.le_top y₁⟩
  have ha1 : M.lt x0 a x1 := ⟨h.le_top a, h.ne_x1_of_lt h₁⟩
  obtain ⟨T, hT⟩ := h.exists_seg ha1
  have hTc := h.car_eq_Icc ha1 hT
  have hin : ∀ y, M.lt x0 a y → y ≠ x1 → y ∈ M.intr T := fun y hy hy1 =>
    ⟨by rw [hTc]; exact ⟨hy.1, h.le_top y⟩, by rw [hT]; simp [Ne.symm hy.2, hy1]⟩
  obtain ⟨w, hw, hsub⟩ := h.ax.F3' T a (by rw [hT]; simp) y₁ (hin y₁ h₁ e₁) y₂ (hin y₂ h₂ e₂)
  have hwa : w ≠ a := fun e => hw.2 (by rw [e, hT]; simp)
  have hwT : M.lt x0 a w := by
    have hw1 := hw.1; rw [hTc] at hw1; exact ⟨hw1.1, Ne.symm hwa⟩
  obtain ⟨T₁, hT₁, -⟩ := h.ax.F1 T a (by rw [hT]; simp) y₁ (hin y₁ h₁ e₁).1 (Ne.symm h₁.2)
  obtain ⟨T₂, hT₂, -⟩ := h.ax.F1 T a (by rw [hT]; simp) y₂ (hin y₂ h₂ e₂).1 (Ne.symm h₂.2)
  obtain ⟨Tw, hTw, -⟩ := h.ax.F1 T a (by rw [hT]; simp) w hw.1 hwa
  have hm := hsub T₁ T₂ Tw hT₁ hT₂ hTw (h.ax.right_mem hTw.2)
  rw [h.car_eq_Icc h₁ hT₁.2, h.car_eq_Icc h₂ hT₂.2] at hm
  exact ⟨w, hwT, hm.1.2, hm.2.2⟩

/-- Property b′) of page 12: locally directed upwards, from F′3 at the
extremity `a` of `[x₀, a]`. -/
theorem dir_up {a y₁ y₂ : L} (h₁ : M.lt x0 y₁ a) (h₂ : M.lt x0 y₂ a) :
    ∃ y, M.le x0 y₁ y ∧ M.le x0 y₂ y ∧ M.lt x0 y a := by
  by_cases e₁ : y₁ = x0
  · exact ⟨y₂, e₁ ▸ h.bot_le y₂, le_refl' x0 y₂, h₂⟩
  by_cases e₂ : y₂ = x0
  · exact ⟨y₁, le_refl' x0 y₁, e₂ ▸ h.bot_le y₁, h₁⟩
  have ha0 := h.ne_x0_of_lt h₁
  have h0a : M.lt x0 x0 a := ⟨h.bot_le a, Ne.symm ha0⟩
  obtain ⟨T, hT⟩ := h.exists_x0 ha0
  have hTc := h.car_eq_Icc h0a hT
  have haT : a ∈ M.bd T := by rw [hT]; simp
  have hin : ∀ y, M.lt x0 y a → y ≠ x0 → y ∈ M.intr T := fun y hy hy0 =>
    ⟨by rw [hTc]; exact ⟨h.bot_le y, hy.1⟩, by rw [hT]; simp [hy.2, hy0]⟩
  obtain ⟨w, hw, hsub⟩ := h.ax.F3' T a haT y₁ (hin y₁ h₁ e₁) y₂ (hin y₂ h₂ e₂)
  have hwa : w ≠ a := fun e => hw.2 (by rw [e]; exact haT)
  have hwT : M.lt x0 w a := by
    have hw1 := hw.1; rw [hTc] at hw1; exact ⟨hw1.2, hwa⟩
  obtain ⟨T₁, hT₁, -⟩ := h.ax.F1 T a haT y₁ (hin y₁ h₁ e₁).1 h₁.2
  obtain ⟨T₂, hT₂, -⟩ := h.ax.F1 T a haT y₂ (hin y₂ h₂ e₂).1 h₂.2
  obtain ⟨Tw, hTw, -⟩ := h.ax.F1 T a haT w hw.1 hwa
  have hm := hsub T₁ T₂ Tw hT₁ hT₂ hTw (h.ax.right_mem hTw.2)
  rw [h.car_eq_Icc h₁ (by rw [hT₁.2, pair_comm]), h.car_eq_Icc h₂ (by rw [hT₂.2, pair_comm])]
    at hm
  exact ⟨w, hm.1.1, hm.2.1, hwT⟩

/-- The order of page 11 on the lieux of the segment model. -/
abbrev toPartialOrder : PartialOrder L where
  le := M.le x0
  le_refl := le_refl' x0
  le_trans := fun _ _ _ => h.le_trans'
  le_antisymm := fun _ _ => h.le_antisymm'

end SegModel

end Data

/-- Locally directed downwards (« localement filtrant décroissant », page 12). -/
def LocDirDown (α : Type*) [Preorder α] : Prop :=
  ∀ x y₁ y₂ : α, x < y₁ → x < y₂ → ∃ y, x < y ∧ y ≤ y₁ ∧ y ≤ y₂

/-- Locally directed upwards (« localement filtrant croissant », page 12). -/
def LocDirUp (α : Type*) [Preorder α] : Prop :=
  ∀ x y₁ y₂ : α, y₁ < x → y₂ < x → ∃ y, y₁ ≤ y ∧ y₂ ≤ y ∧ y < x

namespace Data.SegModel

variable {L S : Type*} {M : Data L S} {I : S} {x0 x1 : L} (h : M.SegModel I x0 x1)
include h

theorem lt_iff {a b : L} : (letI := h.toPartialOrder; a < b) ↔ M.lt x0 a b := by
  let _ : PartialOrder L := h.toPartialOrder
  exact lt_iff_le_and_ne

/-- **Pages 10–13, forward direction.** In a model which is a single segment
`I = L` with `∂I = {x₀, x₁}`, the order of page 11 has least element `x₀` and
greatest element `x₁`, distinct; it is dense and locally directed downwards and
upwards; every segment is an interval `[a, b]`, `a < b`, with `∂ = {a, b}`, and
every such interval is carried by exactly one segment. Only F1, F2, F′3 and F4
are used. -/
theorem biorder :
    letI := h.toPartialOrder
    (∀ a, x0 ≤ a) ∧ (∀ a, a ≤ x1) ∧ x0 ≠ x1 ∧ DenselyOrdered L ∧ LocDirDown L ∧
      LocDirUp L ∧ (∀ J, ∃ a b, a < b ∧ M.car J = Icc a b ∧ M.bd J = {a, b}) ∧
      (∀ a b : L, a < b → ∃! J, M.car J = Icc a b ∧ M.bd J = {a, b}) := by
  let _ : PartialOrder L := h.toPartialOrder
  have hlt : ∀ a b : L, a < b ↔ M.lt x0 a b := fun a b => h.lt_iff
  refine ⟨h.bot_le, h.le_top, h.ax.ne_of_bd h.bd_eq, ⟨fun a b hab => ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c, h1, h2⟩ := h.dense ((hlt a b).1 hab)
    exact ⟨c, (hlt _ _).2 h1, (hlt _ _).2 h2⟩
  · intro a y₁ y₂ h₁ h₂
    obtain ⟨y, hy, hy₁, hy₂⟩ := h.dir_down ((hlt _ _).1 h₁) ((hlt _ _).1 h₂)
    exact ⟨y, (hlt _ _).2 hy, hy₁, hy₂⟩
  · intro a y₁ y₂ h₁ h₂
    obtain ⟨y, hy₁, hy₂, hy⟩ := h.dir_up ((hlt _ _).1 h₁) ((hlt _ _).1 h₂)
    exact ⟨y, hy₁, hy₂, (hlt _ _).2 hy⟩
  · intro J
    obtain ⟨u, v, -, hJ⟩ := h.ax.bd_pair J
    rcases h.lt_or_lt_of_bd hJ with huv | hvu
    · exact ⟨u, v, (hlt _ _).2 huv, h.car_eq_Icc huv hJ, hJ⟩
    · rw [pair_comm] at hJ
      exact ⟨v, u, (hlt _ _).2 hvu, h.car_eq_Icc hvu hJ, hJ⟩
  · intro a b hab
    obtain ⟨K, hK⟩ := h.exists_seg ((hlt a b).1 hab)
    exact ⟨K, ⟨h.car_eq_Icc ((hlt a b).1 hab) hK, hK⟩,
      fun K' hK' => h.bd_inj (hK'.2.trans hK.symm)⟩

/-- **Page 13.** Exchanging the extremities replaces the order by its opposite:
a segment structure is a biorder. -/
theorem le_swap (a b : L) : M.le x1 a b ↔ M.le x0 b a := by
  have h' : M.SegModel I x1 x0 := ⟨h.ax, h.car_eq, by rw [h.bd_eq, pair_comm]⟩
  by_cases hb : b = x1
  · rw [hb, h'.le_x0]
    exact ⟨fun e => by rw [e]; exact le_refl' x0 x1, fun hx => h.le_antisymm' (h.le_top a) hx⟩
  obtain ⟨J, hJ⟩ := h'.exists_x0 hb
  have hb1 : M.lt x0 b x1 := ⟨h.le_top b, hb⟩
  rw [h'.le_iff hJ, h.car_eq_Icc hb1 (by rw [hJ, pair_comm])]
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, h.le_top a⟩⟩

end Data.SegModel

/-! ## The converse: the intervals of a bounded, dense, locally directed poset -/

/-- The segments of a poset: the pairs `x < y`. -/
def Seg (α : Type*) [Preorder α] := {p : α × α // p.1 < p.2}

/-- The model of page 12's converse: the segment `(x, y)` carries the interval
`[x, y]` and has extremities `{x, y}`. -/
def intervals (α : Type*) [Preorder α] : Data α (Seg α) where
  car p := Icc p.1.1 p.1.2
  bd p := {p.1.1, p.1.2}

section Converse

variable {α : Type*} [PartialOrder α]

theorem intervals_eq_of_bd {p : Seg α} {u v : α} (hp : (intervals α).bd p = {u, v})
    (huv : u < v) : p = ⟨(u, v), huv⟩ := by
  rcases pair_eq_pair_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · have := p.2; rw [h1, h2] at this; exact absurd huv (lt_asymm this)

theorem intervals_car_of_bd {p : Seg α} {u v : α} (hp : (intervals α).bd p = {u, v})
    (huv : u < v) : (intervals α).car p = Icc u v := by
  rw [intervals_eq_of_bd hp huv]; rfl

theorem intervals_mem_bd {p : Seg α} {x : α} :
    x ∈ (intervals α).bd p ↔ x = p.1.1 ∨ x = p.1.2 := by
  simp [intervals]

theorem intervals_intr {p : Seg α} {z : α} :
    z ∈ (intervals α).intr p ↔ p.1.1 < z ∧ z < p.1.2 := by
  simp only [Data.intr, intervals, mem_sdiff, mem_Icc, mem_insert_iff, mem_singleton_iff,
    not_or]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), lt_of_le_of_ne h2 h4⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2.le⟩, h1.ne', h2.ne⟩

/-- The sub-segment `(a, z)` of `(a, b)` issued from `a`. -/
theorem intervals_isSub_left {a b z : α} (hab : a < b) (haz : a < z) (hzb : z ≤ b) :
    (intervals α).IsSub ⟨(a, b), hab⟩ a z ⟨(a, z), haz⟩ :=
  ⟨Icc_subset_Icc le_rfl hzb, rfl⟩

/-- The sub-segment `(z, b)` of `(a, b)` issued from `b`. -/
theorem intervals_isSub_right {a b z : α} (hab : a < b) (hzb : z < b) (haz : a ≤ z) :
    (intervals α).IsSub ⟨(a, b), hab⟩ b z ⟨(z, b), hzb⟩ :=
  ⟨Icc_subset_Icc haz le_rfl, pair_comm _ _⟩

theorem intervals_sameBranch_up {x b d : α} (hxb : x < b) (hxd : x < d)
    [DenselyOrdered α] (hd : LocDirDown α) :
    (intervals α).SameBranch x ⟨(x, d), hxd⟩ ⟨(x, b), hxb⟩ := by
  obtain ⟨y, hxy, hyd, hyb⟩ := hd x d b hxd hxb
  obtain ⟨z, hxz, hzy⟩ := exists_between hxy
  refine ⟨by simp [intervals], by simp [intervals], z,
    ⟨intervals_intr.2 ⟨hxz, hzy.trans_le hyd⟩, intervals_intr.2 ⟨hxz, hzy.trans_le hyb⟩⟩,
    ⟨(x, z), hxz⟩, intervals_isSub_left hxd hxz (hzy.le.trans hyd),
    intervals_isSub_left hxb hxz (hzy.le.trans hyb)⟩

theorem intervals_sameBranch_down {x a c : α} (hax : a < x) (hcx : c < x)
    [DenselyOrdered α] (hu : LocDirUp α) :
    (intervals α).SameBranch x ⟨(c, x), hcx⟩ ⟨(a, x), hax⟩ := by
  obtain ⟨y, hcy, hay, hyx⟩ := hu x c a hcx hax
  obtain ⟨z, hyz, hzx⟩ := exists_between hyx
  refine ⟨by simp [intervals], by simp [intervals], z,
    ⟨intervals_intr.2 ⟨hcy.trans_lt hyz, hzx⟩, intervals_intr.2 ⟨hay.trans_lt hyz, hzx⟩⟩,
    ⟨(z, x), hzx⟩, intervals_isSub_right hcx hzx (hcy.trans hyz.le),
    intervals_isSub_right hax hzx (hay.trans hyz.le)⟩

/-- **Page 12, converse.** On a dense poset, locally directed downwards and
upwards, the intervals `[x, y]`, `x < y`, satisfy F1–F5 and F′3. (No bound is
needed for this; F4 holds without its regularity hypothesis.) -/
theorem intervals_axioms [DenselyOrdered α] (hd : LocDirDown α) (hu : LocDirUp α) :
    (intervals α).Axioms where
  bd_pair p := ⟨p.1.1, p.1.2, p.2.ne, rfl⟩
  bd_sub p := by
    rintro x (rfl | rfl)
    · exact ⟨le_rfl, p.2.le⟩
    · exact ⟨p.2.le, le_rfl⟩
  F1 := by
    rintro ⟨⟨a, b⟩, hab⟩ x hx z hz hzx
    rcases intervals_mem_bd.1 hx with rfl | rfl
    · have hxz : x < z := lt_of_le_of_ne hz.1 (Ne.symm hzx)
      exact ⟨⟨(x, z), hxz⟩, intervals_isSub_left hab hxz hz.2,
        fun J hJ => intervals_eq_of_bd hJ.2 hxz⟩
    · have hzx' : z < x := lt_of_le_of_ne hz.2 hzx
      exact ⟨⟨(z, x), hzx'⟩, intervals_isSub_right hab hzx' hz.1,
        fun J hJ => intervals_eq_of_bd (hJ.2.trans (pair_comm _ _)) hzx'⟩
  F2_intr := by
    rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨c, intervals_intr.2 ⟨hac, hcb⟩⟩
  F2 := by
    rintro ⟨⟨a, b⟩, hab⟩ x y z hxy hz Jx Jy hJx hJy
    obtain ⟨haz, hzb⟩ := intervals_intr.1 hz
    -- the sub-segments issued from `z`, inside `[a, b]`
    have side : ∀ J : Seg α, (intervals α).car J ⊆ Icc a b → z ∈ (intervals α).bd J →
        (intervals α).car J ⊆ Icc a z ∨ (intervals α).car J ⊆ Icc z b := by
      intro J hJ hzJ
      have h2 : J.1.2 ∈ Icc a b := hJ ⟨J.2.le, le_rfl⟩
      have h1 : J.1.1 ∈ Icc a b := hJ ⟨le_rfl, J.2.le⟩
      rcases intervals_mem_bd.1 hzJ with e | e
      · right; show Icc J.1.1 J.1.2 ⊆ _; rw [← e]; exact Icc_subset_Icc le_rfl h2.2
      · left; show Icc J.1.1 J.1.2 ⊆ _; rw [← e]; exact Icc_subset_Icc h1.1 le_rfl
    have hI : Icc a z ∩ Icc z b = {z} := Icc_inter_Icc_eq_singleton haz.le hzb.le
    rcases pair_eq_pair_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [intervals_car_of_bd hJx.2 haz,
        intervals_car_of_bd (hJy.2.trans (pair_comm _ _)) hzb]
      exact ⟨hI, side⟩
    · rw [intervals_car_of_bd (hJx.2.trans (pair_comm _ _)) hzb,
        intervals_car_of_bd hJy.2 haz, inter_comm]
      exact ⟨hI, fun J hJ hzJ => (side J hJ hzJ).symm⟩
  F3 := by
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ x hxI hxJ
    rcases intervals_mem_bd.1 hxI with rfl | rfl <;>
      rcases intervals_mem_bd.1 hxJ with e | e <;> dsimp only at e <;> subst e
    · obtain ⟨y, hxy, hyb, hyd⟩ := hd _ b d hab hcd
      exact ⟨y, ⟨hxy.le, hyb⟩, hxy.ne', y, ⟨hxy.le, hyd⟩, hxy.ne', ⟨(_, y), hxy⟩,
        ⟨(_, y), hxy⟩, intervals_isSub_left hab hxy hyb, intervals_isSub_left hcd hxy hyd,
        Or.inl rfl⟩
    · refine ⟨b, ⟨hab.le, le_rfl⟩, hab.ne', c, ⟨le_rfl, hcd.le⟩, hcd.ne, ⟨(_, b), hab⟩,
        ⟨(c, _), hcd⟩, ⟨subset_rfl, rfl⟩, ⟨subset_rfl, pair_comm _ _⟩, Or.inr ?_⟩
      show Icc _ b ∩ Icc c _ = _
      rw [inter_comm]; exact Icc_inter_Icc_eq_singleton hcd.le hab.le
    · refine ⟨a, ⟨le_rfl, hab.le⟩, hab.ne, d, ⟨hcd.le, le_rfl⟩, hcd.ne', ⟨(a, _), hab⟩,
        ⟨(_, d), hcd⟩, ⟨subset_rfl, pair_comm _ _⟩, ⟨subset_rfl, rfl⟩, Or.inr ?_⟩
      exact Icc_inter_Icc_eq_singleton hab.le hcd.le
    · obtain ⟨y, hay, hcy, hyx⟩ := hu _ a c hab hcd
      exact ⟨y, ⟨hay, hyx.le⟩, hyx.ne, y, ⟨hcy, hyx.le⟩, hyx.ne, ⟨(y, _), hyx⟩,
        ⟨(y, _), hyx⟩, intervals_isSub_right hab hyx hay, intervals_isSub_right hcd hyx hcy,
        Or.inl rfl⟩
  F3' := by
    rintro ⟨⟨a, b⟩, hab⟩ x hx u hu' v hv'
    obtain ⟨hau, hub⟩ := intervals_intr.1 hu'
    obtain ⟨hav, hvb⟩ := intervals_intr.1 hv'
    rcases intervals_mem_bd.1 hx with rfl | rfl
    · obtain ⟨w, hxw, hwu, hwv⟩ := hd _ u v hau hav
      refine ⟨w, intervals_intr.2 ⟨hxw, hwu.trans_lt hub⟩, fun Iu Iv Iw hIu hIv hIw => ?_⟩
      rw [intervals_car_of_bd hIu.2 hau, intervals_car_of_bd hIv.2 hav,
        intervals_car_of_bd hIw.2 hxw]
      exact subset_inter (Icc_subset_Icc le_rfl hwu) (Icc_subset_Icc le_rfl hwv)
    · obtain ⟨w, huw, hvw, hwx⟩ := hu _ u v hub hvb
      refine ⟨w, intervals_intr.2 ⟨hau.trans_le huw, hwx⟩, fun Iu Iv Iw hIu hIv hIw => ?_⟩
      rw [intervals_car_of_bd (hIu.2.trans (pair_comm _ _)) hub,
        intervals_car_of_bd (hIv.2.trans (pair_comm _ _)) hvb,
        intervals_car_of_bd (hIw.2.trans (pair_comm _ _)) hwx]
      exact subset_inter (Icc_subset_Icc huw le_rfl) (Icc_subset_Icc hvw le_rfl)
  F4 := by
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ x y z - hint hp hq
    have hint' : Icc a b ∩ Icc c d = {z} := hint
    rcases pair_eq_pair_iff.1 hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases pair_eq_pair_iff.1 hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- both below `z`: excluded by local directedness upwards
      obtain ⟨w, haw, hcw, hwz⟩ := hu _ a c hab hcd
      have : w ∈ Icc a _ ∩ Icc c _ := ⟨⟨haw, hwz.le⟩, ⟨hcw, hwz.le⟩⟩
      rw [hint'] at this; exact absurd this hwz.ne
    · refine ⟨⟨(a, d), hab.trans hcd⟩, ⟨union_subset (Icc_subset_Icc le_rfl hcd.le)
        (Icc_subset_Icc hab.le le_rfl), rfl⟩, fun J hJ => intervals_eq_of_bd hJ.2 _⟩
    · refine ⟨⟨(c, b), hcd.trans hab⟩, ⟨union_subset (Icc_subset_Icc hcd.le le_rfl)
        (Icc_subset_Icc le_rfl hab.le), pair_comm _ _⟩,
        fun J hJ => intervals_eq_of_bd (hJ.2.trans (pair_comm _ _)) _⟩
    · -- both above `z`: excluded by local directedness downwards
      obtain ⟨w, hzw, hwb, hwd⟩ := hd _ b d hab hcd
      have : w ∈ Icc _ b ∩ Icc _ d := ⟨⟨hzw.le, hwb⟩, ⟨hzw.le, hwd⟩⟩
      rw [hint'] at this; exact absurd this hzw.ne'
  F5 := by
    rintro x ⟨⟨⟨a, b⟩, hab⟩, hx⟩
    obtain ⟨hax, hxb⟩ := intervals_intr.1 hx
    refine ⟨⟨(a, x), hax⟩, ⟨(x, b), hxb⟩, by simp [intervals], by simp [intervals], ?_, ?_⟩
    · rintro ⟨-, -, z, ⟨hz1, hz2⟩, -⟩
      exact lt_asymm (intervals_intr.1 hz1).2 (intervals_intr.1 hz2).1
    · rintro ⟨⟨c, d⟩, hcd⟩ hxK
      rcases intervals_mem_bd.1 hxK with e | e <;> dsimp only at e <;> subst e
      · exact Or.inr (intervals_sameBranch_up hxb hcd hd)
      · exact Or.inl (intervals_sameBranch_down hax hcd hu)

variable [BoundedOrder α]

/-- The whole segment `(⊥, ⊤)`. -/
def topSeg (h : (⊥ : α) ≠ ⊤) : Seg α := ⟨(⊥, ⊤), bot_lt_iff_ne_bot.2 h.symm⟩

/-- **Page 12, converse.** A bounded poset with `⊥ ≠ ⊤`, dense and locally
directed both ways, is a model-segment with extremities `⊥, ⊤`. -/
theorem intervals_segModel [DenselyOrdered α] (hd : LocDirDown α) (hu : LocDirUp α)
    (h : (⊥ : α) ≠ ⊤) : (intervals α).SegModel (topSeg h) ⊥ ⊤ :=
  ⟨intervals_axioms hd hu, Icc_bot_top, rfl⟩

/-- The order read back from the model-segment at `⊥` (page 11) is the given
order: the two constructions are inverse to each other. -/
theorem intervals_le_iff (a b : α) : (intervals α).le ⊥ a b ↔ a ≤ b := by
  constructor
  · rintro (rfl | ⟨J, hJ, ha⟩)
    · exact le_rfl
    · rcases pair_eq_pair_iff.1 hJ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : a ∈ Icc J.1.1 J.1.2 := ha
        rw [h1, h2] at this; exact this.2
      · have := J.2; rw [h1, h2] at this; exact absurd this not_lt_bot
  · intro hab
    by_cases e : a = b
    · exact Or.inl e
    have hb : (⊥ : α) < b := bot_lt_iff_ne_bot.2 fun hb => e (le_bot_iff.1 (hb ▸ hab) ▸ hb.symm)
    exact Or.inr ⟨⟨(⊥, b), hb⟩, rfl, ⟨bot_le, hab⟩⟩

end Converse

/-! ## A segment model whose order is not total -/

namespace Diamond

/-- The open cone order on `ℚ²`: `p ≺ q` iff `|q₂ − p₂| < q₁ − p₁`. -/
def cone (p q : ℚ × ℚ) : Prop := q.2 - p.2 < q.1 - p.1 ∧ p.2 - q.2 < q.1 - p.1

theorem cone_trans {p q r : ℚ × ℚ} (h1 : cone p q) (h2 : cone q r) : cone p r :=
  ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩

theorem cone_irrefl (p : ℚ × ℚ) : ¬ cone p p := fun h => by linarith [h.1]

theorem cone_asymm {p q : ℚ × ℚ} (h : cone p q) : ¬ cone q p := fun h' => by
  linarith [h.1, h'.1]

/-- `p ≤ q` iff `p = q` or `p ≺ q`. -/
def cle (p q : ℚ × ℚ) : Prop := p = q ∨ cone p q

theorem cle_cone {p q r : ℚ × ℚ} (h1 : cle p q) (h2 : cone q r) : cone p r :=
  h1.elim (· ▸ h2) (cone_trans · h2)

theorem cone_cle {p q r : ℚ × ℚ} (h1 : cone p q) (h2 : cle q r) : cone p r :=
  h2.elim (· ▸ h1) (cone_trans h1 ·)

/-- The lower end `(0, 0)`. -/
def lo : ℚ × ℚ := (0, 0)

/-- The upper end `(2, 0)`. -/
def hi : ℚ × ℚ := (2, 0)

theorem cone_lo_hi : cone lo hi := by norm_num [cone, lo, hi]

/-- The points between `(0, 0)` and `(2, 0)` for the cone order: an open
square standing on a vertex, with its two ends. -/
def T : Type := {p : ℚ × ℚ // cle lo p ∧ cle p hi}

instance : PartialOrder T where
  le a b := cle a.1 b.1
  le_refl _ := Or.inl rfl
  le_trans a b c := by
    rintro (h | h) (h' | h')
    · exact Or.inl (h.trans h')
    · exact Or.inr (by rw [h]; exact h')
    · exact Or.inr (by rw [← h']; exact h)
    · exact Or.inr (cone_trans h h')
  le_antisymm a b := by
    rintro (h | h) (h' | h')
    · exact Subtype.ext h
    · exact Subtype.ext h
    · exact Subtype.ext h'.symm
    · exact absurd h' (cone_asymm h)

instance : BoundedOrder T where
  bot := ⟨lo, Or.inl rfl, Or.inr cone_lo_hi⟩
  top := ⟨hi, Or.inr cone_lo_hi, Or.inl rfl⟩
  bot_le a := a.2.1
  le_top a := a.2.2

theorem lt_iff {a b : T} : a < b ↔ cone a.1 b.1 :=
  lt_iff_le_and_ne.trans ⟨fun ⟨h, hne⟩ => h.resolve_left fun e => hne (Subtype.ext e),
    fun h => ⟨Or.inr h, by rintro rfl; exact cone_irrefl _ h⟩⟩

/-- A point of `ℚ²` strictly between two points of `T` is in `T`. -/
def mk (m : ℚ × ℚ) (a b : T) (h1 : cone a.1 m) (h2 : cone m b.1) : T :=
  ⟨m, Or.inr (cle_cone a.2.1 h1), Or.inr (cone_cle h2 b.2.2)⟩

/-- How far `q` is inside the cone at `p`. -/
def gap (p q : ℚ × ℚ) : ℚ := min (q.1 - p.1 - (q.2 - p.2)) (q.1 - p.1 - (p.2 - q.2))

theorem gap_pos {p q : ℚ × ℚ} (h : cone p q) : 0 < gap p q :=
  lt_min (by linarith [h.1]) (by linarith [h.2])

theorem shift_up {p q : ℚ × ℚ} {ε : ℚ} (hε : 0 < ε) (hg : ε < gap p q) :
    cone p (p.1 + ε, p.2) ∧ cone (p.1 + ε, p.2) q := by
  have h1 := lt_of_lt_of_le hg (min_le_left _ _)
  have h2 := lt_of_lt_of_le hg (min_le_right _ _)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp only <;> linarith

theorem shift_down {p q : ℚ × ℚ} {ε : ℚ} (hε : 0 < ε) (hg : ε < gap q p) :
    cone q (p.1 - ε, p.2) ∧ cone (p.1 - ε, p.2) p := by
  have h1 := lt_of_lt_of_le hg (min_le_left _ _)
  have h2 := lt_of_lt_of_le hg (min_le_right _ _)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp only <;> linarith

instance : DenselyOrdered T := ⟨fun a b hab => by
  have h := lt_iff.1 hab
  have hm : cone a.1 ((a.1.1 + b.1.1) / 2, (a.1.2 + b.1.2) / 2) ∧
      cone ((a.1.1 + b.1.1) / 2, (a.1.2 + b.1.2) / 2) b.1 := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp only <;> linarith [h.1, h.2]
  exact ⟨mk _ a b hm.1 hm.2, lt_iff.2 hm.1, lt_iff.2 hm.2⟩⟩

theorem locDirDown : LocDirDown T := by
  intro x y₁ y₂ h₁ h₂
  have g₁ := gap_pos (lt_iff.1 h₁)
  have g₂ := gap_pos (lt_iff.1 h₂)
  have m₀ := lt_min g₁ g₂
  have m₁ := min_le_left (gap x.1 y₁.1) (gap x.1 y₂.1)
  have m₂ := min_le_right (gap x.1 y₁.1) (gap x.1 y₂.1)
  obtain ⟨ε, hε, e₁, e₂⟩ : ∃ ε : ℚ, 0 < ε ∧ ε < gap x.1 y₁.1 ∧ ε < gap x.1 y₂.1 :=
    ⟨min (gap x.1 y₁.1) (gap x.1 y₂.1) / 2, by linarith, by linarith, by linarith⟩
  obtain ⟨k₁, k₂⟩ := shift_up hε e₁
  exact ⟨mk _ x y₁ k₁ k₂, lt_iff.2 k₁, Or.inr k₂, Or.inr (shift_up hε e₂).2⟩

theorem locDirUp : LocDirUp T := by
  intro x y₁ y₂ h₁ h₂
  have g₁ := gap_pos (lt_iff.1 h₁)
  have g₂ := gap_pos (lt_iff.1 h₂)
  have m₀ := lt_min g₁ g₂
  have m₁ := min_le_left (gap y₁.1 x.1) (gap y₂.1 x.1)
  have m₂ := min_le_right (gap y₁.1 x.1) (gap y₂.1 x.1)
  obtain ⟨ε, hε, e₁, e₂⟩ : ∃ ε : ℚ, 0 < ε ∧ ε < gap y₁.1 x.1 ∧ ε < gap y₂.1 x.1 :=
    ⟨min (gap y₁.1 x.1) (gap y₂.1 x.1) / 2, by linarith, by linarith, by linarith⟩
  obtain ⟨k₁, k₂⟩ := shift_down hε e₁
  exact ⟨mk _ y₁ x k₁ k₂, Or.inr k₁, Or.inr (shift_down hε e₂).1, lt_iff.2 k₂⟩

/-- The two points `(1, 1/2)` and `(1, −1/2)` of `T` are not comparable. -/
theorem not_total : ∃ a b : T, ¬ a ≤ b ∧ ¬ b ≤ a := by
  refine ⟨⟨(1, 1 / 2), Or.inr ?_, Or.inr ?_⟩, ⟨(1, -1 / 2), Or.inr ?_, Or.inr ?_⟩, ?_, ?_⟩
  · norm_num [cone, lo]
  · norm_num [cone, hi]
  · norm_num [cone, lo]
  · norm_num [cone, hi]
  · rintro (h | h) <;> norm_num [cone, Prod.ext_iff] at h
  · rintro (h | h) <;> norm_num [cone, Prod.ext_iff] at h

/-- **Page 12, « the order need not be total ».** `T` is a bounded poset with
`⊥ ≠ ⊤`, dense and locally directed both ways, not totally ordered; its
intervals form a model-segment. -/
theorem example_segModel :
    (⊥ : T) ≠ ⊤ ∧ (∃ a b : T, ¬ a ≤ b ∧ ¬ b ≤ a) ∧
      ∃ h : (⊥ : T) ≠ ⊤, (intervals T).SegModel (topSeg h) ⊥ ⊤ := by
  have h : (⊥ : T) ≠ ⊤ := fun e => by
    have : lo = hi := congrArg Subtype.val e
    norm_num [lo, hi] at this
  exact ⟨h, not_total, h, intervals_segModel locDirDown locDirUp h⟩

end Diamond

end Grothendieck.Folder156_1
