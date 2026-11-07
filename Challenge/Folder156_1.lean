module

public import Mathlib

@[expose] public section

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

theorem mem_car (a : L) : a ∈ M.car I := h.car_eq ▸ mem_univ a

theorem isSub {J : S} {e w : L} (hJ : M.bd J = {e, w}) : M.IsSub I e w J :=
  ⟨h.car_eq ▸ subset_univ _, hJ⟩

theorem uniq0 {J J' : S} {b : L} (hJ : M.bd J = {x0, b}) (hJ' : M.bd J' = {x0, b}) :
    J = J' :=
  h.ax.sub_unique h.x0_bd (h.mem_car b) (h.ax.ne_of_bd hJ).symm (h.isSub hJ) (h.isSub hJ')

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
  sorry

end Data.SegModel

end Grothendieck.Folder156_1
