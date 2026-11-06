module

public import Mathlib.Topology.Closure
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.WellFounded
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Topology.Connected.Basic

@[expose] public section


/-!
# Folder 121, pages 3–16: the coarsest admissible cellular decomposition

The modernised reading `transcripts/121/121.modern.tex` (§§ 1–3, pages 3 to 16) puts on a
topological space `X` a Boolean algebra `𝓕` of parts with

> c bis) `A ∈ 𝓕 ⇒ Ā ∈ 𝓕`; d) every `A ∈ 𝓕` contains a dense open part of its closure;
> e) every decreasing sequence of closed members, each rare in the one before, ends at `∅`,

proves (page 8) that the boundary of a member is rare, and states (page 14):

> **Proposition.** Let `𝓕` satisfy a) to e) and `𝓛 ⊂ 𝓕` finite. There is an `𝓕`-admissible
> cellular decomposition of which the members of `𝓛` are unions of cells, and among them one
> coarser than all the others.

A cellular decomposition (page 10) is a finite partition with the frontier condition (1) (the
closure of a cell is a union of cells) and (2) (distinct cells have distinct closures). The page
proves existence by induction, removing the union of the boundaries and stopping by e); it asserts
« la plus grossière » without argument. This is finding `121-coarsest-cell-decomposition` of
`src/content/findings.ts`; proving it says only that the statement holds, not whether it is in
the literature.

What is formalised.

* `Tame`: conditions a) to e), with d) read relative to the closure, as the reading does.
* `Tame.rare_bd`: page 8, the boundary `Ā ∩ cl(Z ∖ A)` of a member is rare (relative to a closed
  member `Z`).
* `page14`: the proposition, existence and coarsest, for `X`; `exists_coarsest` for every closed
  member `Z` in place of `X`, which is what the induction on e) needs.
* `subset_bd`: the edition's argument for « la plus grossière »: in a decomposition for which `Y`
  is a union of cells, a cell meeting the boundary of `Y` lies in it.

Not formalised: the connected-cells version of page 16 (condition f)), the corollaries of
page 15, the regular decompositions of page 17.
-/

namespace Grothendieck.Folder121

open Set

variable {X : Type*} [TopologicalSpace X]

/-- `B` is rare in `Z`: no nonempty relatively open part of `Z` lies in `B`. -/
def Rare (B Z : Set X) : Prop := ∀ V, IsOpen V → V ∩ Z ⊆ B → V ∩ Z = ∅

/-- Conditions a) to e) of pages 3–5 on a family `F` of parts of `X`. -/
structure Tame (F : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ F
  compl_mem : ∀ A ∈ F, Aᶜ ∈ F
  union_mem : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F
  closure_mem : ∀ A ∈ F, closure A ∈ F
  dense_open : ∀ A ∈ F, ∃ G, IsOpen G ∧ G ∩ closure A ⊆ A ∧ closure A ⊆ closure (G ∩ closure A)
  dcc : ∀ A : ℕ → Set X, (∀ n, A n ∈ F ∧ IsClosed (A n)) →
    (∀ n, A (n + 1) ⊆ A n ∧ Rare (A (n + 1)) (A n)) → ∃ n, A n = ∅

variable {F : Set (Set X)}

namespace Tame

variable (hF : Tame F)
include hF

theorem inter_mem {A B : Set X} (hA : A ∈ F) (hB : B ∈ F) : A ∩ B ∈ F := by
  have := hF.compl_mem _ (hF.union_mem _ (hF.compl_mem _ hA) _ (hF.compl_mem _ hB))
  rwa [compl_union, compl_compl, compl_compl] at this

theorem diff_mem {A B : Set X} (hA : A ∈ F) (hB : B ∈ F) : A \ B ∈ F :=
  hF.inter_mem hA (hF.compl_mem _ hB)

theorem univ_mem : univ ∈ F := by simpa using hF.compl_mem _ hF.empty_mem

theorem biUnion_mem {ι : Type*} (s : Finset ι) (f : ι → Set X) (h : ∀ i ∈ s, f i ∈ F) :
    (⋃ i ∈ s, f i) ∈ F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hF.empty_mem
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact hF.union_mem _ (h a (Finset.mem_insert_self a s)) _
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem biInter_mem {ι : Type*} (s : Finset ι) (f : ι → Set X) (h : ∀ i ∈ s, f i ∈ F) :
    (⋂ i ∈ s, f i) ∈ F := by
  have := hF.compl_mem _ (hF.biUnion_mem s (fun i => (f i)ᶜ) fun i hi => hF.compl_mem _ (h i hi))
  simpa [compl_iUnion] using this

end Tame

/-- The boundary of `A` relative to `Z`. -/
def bd (Z A : Set X) : Set X := closure A ∩ closure (Z \ A)

theorem Tame.bd_mem (hF : Tame F) {Z A : Set X} (hZ : Z ∈ F) (hA : A ∈ F) : bd Z A ∈ F :=
  hF.inter_mem (hF.closure_mem _ hA) (hF.closure_mem _ (hF.diff_mem hZ hA))

theorem isClosed_bd (Z A : Set X) : IsClosed (bd Z A) := isClosed_closure.inter isClosed_closure

/-- **Page 8.** The boundary of a member is rare (here relative to a member `Z`). -/
theorem Tame.rare_bd (hF : Tame F) {Z A : Set X} (hZ : Z ∈ F) (hA : A ∈ F) (hAZ : A ⊆ Z) :
    Rare (bd Z A) Z := by
  intro V hV hVZ
  by_contra hne
  obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
  set O := (closure (Z \ bd Z A))ᶜ with hO
  have hOo : IsOpen O := isClosed_closure.isOpen_compl
  have hU : Z ∩ O ⊆ bd Z A := by
    rintro x ⟨hxZ, hxO⟩
    by_contra h
    exact hxO (subset_closure ⟨hxZ, h⟩)
  have huO : u ∈ O := by
    intro hcl
    rw [mem_closure_iff] at hcl
    obtain ⟨y, hyV, hyZ, hyb⟩ := hcl V hV hu.1
    exact hyb (hVZ ⟨hyV, hyZ⟩)
  have hUA : Z ∩ O ⊆ closure (O ∩ A) := by
    intro x hx
    have hxA : x ∈ closure A := (hU hx).1
    rw [mem_closure_iff] at hxA ⊢
    intro N hN hxN
    obtain ⟨y, ⟨hyN, hyO⟩, hyA⟩ := hxA (N ∩ O) (hN.inter hOo) ⟨hxN, hx.2⟩
    exact ⟨y, hyN, hyO, hyA⟩
  have hW : O ∩ A ∈ F :=
    hF.inter_mem (hF.compl_mem _ (hF.closure_mem _ (hF.diff_mem hZ (hF.bd_mem hZ hA)))) hA
  obtain ⟨G, hG, hGW, hdense⟩ := hF.dense_open _ hW
  have hu' : u ∈ closure (O ∩ A) := hUA ⟨hu.2, huO⟩
  obtain ⟨w, hwG, hwcl⟩ : (G ∩ closure (O ∩ A)).Nonempty :=
    closure_nonempty_iff.mp ⟨u, hdense hu'⟩
  have hwW := hGW ⟨hwG, hwcl⟩
  have hwb : w ∈ closure (Z \ A) := (hU ⟨hAZ hwW.2, hwW.1⟩).2
  rw [mem_closure_iff] at hwb
  obtain ⟨z, ⟨hzG, hzO⟩, hzZ, hzA⟩ := hwb (G ∩ O) (hG.inter hOo) ⟨hwG, hwW.1⟩
  exact hzA (hGW ⟨hzG, hUA ⟨hzZ, hzO⟩⟩).2

theorem Rare.union {B C Z : Set X} (hB : Rare B Z) (hC : Rare C Z) (hBc : IsClosed B) :
    Rare (B ∪ C) Z := by
  intro V hV h
  have h1 : (V \ B) ∩ Z = ∅ :=
    hC _ (hV.sdiff hBc) fun x ⟨⟨hxV, hxB⟩, hxZ⟩ => (h ⟨hxV, hxZ⟩).resolve_left hxB
  refine hB V hV fun x ⟨hxV, hxZ⟩ => ?_
  by_contra hxB
  have : x ∈ (V \ B) ∩ Z := ⟨⟨hxV, hxB⟩, hxZ⟩
  rw [h1] at this
  exact this

theorem rare_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set X) {Z : Set X}
    (h : ∀ i ∈ s, Rare (f i) Z ∧ IsClosed (f i)) : Rare (⋃ i ∈ s, f i) Z := by
  classical
  induction s using Finset.induction_on with
  | empty => intro V _ hV; simpa using hV
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a s)).1.union
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s)).2

/-! ### Cellular decompositions -/

/-- A finite cellular decomposition of `Z` (page 10): nonempty disjoint cells covering `Z`,
the closure of a cell a union of cells (1), distinct cells with distinct closures (2). -/
structure IsDecomp (Z : Set X) (P : Finset (Set X)) : Prop where
  nonempty : ∀ c ∈ P, c.Nonempty
  disjoint : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → Disjoint c d
  cover : ⋃ c ∈ P, c = Z
  frontier : ∀ c ∈ P, ∀ d ∈ P, (closure c ∩ d).Nonempty → d ⊆ closure c
  distinct : ∀ c ∈ P, ∀ d ∈ P, closure c = closure d → c = d

/-- Every member of `L` is a union of cells. -/
def Compat (L P : Finset (Set X)) : Prop := ∀ Y ∈ L, ∀ c ∈ P, c ⊆ Y ∨ Disjoint c Y

/-- An `F`-admissible decomposition of `Z` for which the members of `L` are unions of
cells. -/
def Good (F : Set (Set X)) (L : Finset (Set X)) (Z : Set X) (P : Finset (Set X)) : Prop :=
  IsDecomp Z P ∧ (∀ c ∈ P, c ∈ F) ∧ Compat L P

/-- `P` is coarser than `Q`: every cell of `Q` lies in a cell of `P`. -/
def Coarser (P Q : Finset (Set X)) : Prop := ∀ q ∈ Q, ∃ p ∈ P, q ⊆ p

namespace IsDecomp

variable {Z : Set X} {P : Finset (Set X)}

theorem subset (hP : IsDecomp Z P) {c : Set X} (hc : c ∈ P) : c ⊆ Z :=
  hP.cover ▸ subset_biUnion_of_mem (u := id) hc

theorem exists_mem (hP : IsDecomp Z P) {x : X} (hx : x ∈ Z) : ∃ c ∈ P, x ∈ c := by
  rw [← hP.cover] at hx
  simpa using hx

/-- A cell meeting the closure of a union of cells lies in the closure of one of them. -/
theorem of_closure (hP : IsDecomp Z P) {S : Finset (Set X)} (hS : S ⊆ P) {q : Set X}
    (hq : q ∈ P) (h : (closure (⋃ s ∈ S, s) ∩ q).Nonempty) : ∃ s ∈ S, q ⊆ closure s := by
  rw [Finset.closure_biUnion] at h
  obtain ⟨x, hx1, hx2⟩ := h
  simp only [mem_iUnion] at hx1
  obtain ⟨s, hs, hxs⟩ := hx1
  exact ⟨s, hs, hP.frontier s (hS hs) q hq ⟨x, hxs, hx2⟩⟩

end IsDecomp

/-- The edition's argument for « la plus grossière »: a cell of a decomposition for which
`Y` is a union of cells, and which meets the boundary of `Y`, lies in it. -/
theorem subset_bd {Z Y q : Set X} {Q : Finset (Set X)} (hQ : IsDecomp Z Q)
    (hc : ∀ c ∈ Q, c ⊆ Y ∨ Disjoint c Y) (hq : q ∈ Q) (h : (q ∩ bd Z (Y ∩ Z)).Nonempty) :
    q ⊆ bd Z (Y ∩ Z) := by
  classical
  have hqZ := hQ.subset hq
  rw [bd, sdiff_inter_self_eq_sdiff] at h ⊢
  obtain ⟨x, hxq, hx1, hx2⟩ := h
  have hin : Y ∩ Z ⊆ ⋃ s ∈ Q.filter (· ⊆ Y), s := by
    rintro y ⟨hyY, hyZ⟩
    obtain ⟨c, hc', hyc⟩ := hQ.exists_mem hyZ
    rcases hc c hc' with h' | h'
    · exact mem_biUnion (Finset.mem_filter.2 ⟨hc', h'⟩) hyc
    · exact absurd hyY (h'.notMem_of_mem_left hyc)
  have hout : Z \ Y ⊆ ⋃ s ∈ Q.filter (fun s => Disjoint s Y), s := by
    rintro y ⟨hyZ, hyY⟩
    obtain ⟨c, hc', hyc⟩ := hQ.exists_mem hyZ
    rcases hc c hc' with h' | h'
    · exact absurd (h' hyc) hyY
    · exact mem_biUnion (Finset.mem_filter.2 ⟨hc', h'⟩) hyc
  rcases hc q hq with hqY | hqY
  · refine subset_inter (fun y hy => subset_closure ⟨hqY hy, hqZ hy⟩) ?_
    obtain ⟨s, hs, hqs⟩ := hQ.of_closure (Finset.filter_subset _ _) hq
      ⟨x, closure_mono hout hx2, hxq⟩
    have hs' := (Finset.mem_filter.1 hs)
    exact hqs.trans (closure_mono fun y hy => ⟨hQ.subset hs'.1 hy, hs'.2.notMem_of_mem_left hy⟩)
  · refine subset_inter ?_ (fun y hy => subset_closure ⟨hqZ hy, hqY.notMem_of_mem_left hy⟩)
    obtain ⟨s, hs, hqs⟩ := hQ.of_closure (Finset.filter_subset _ _) hq
      ⟨x, closure_mono hin hx1, hxq⟩
    have hs' := (Finset.mem_filter.1 hs)
    exact hqs.trans (closure_mono fun y hy => ⟨hs'.2 hy, hQ.subset hs'.1 hy⟩)


/-! ### The cells of the open part -/

/-- The cell of `Z ∖ X'` cut out by the pattern `S ⊆ L`. -/
def cell (Z X' : Set X) (L S : Finset (Set X)) : Set X :=
  {y | y ∈ Z ∧ y ∉ X' ∧ ∀ Y ∈ L, y ∈ Y ↔ Y ∈ S}

theorem Tame.cell_mem (hF : Tame F) {Z X' : Set X} {L : Finset (Set X)} (S : Finset (Set X))
    (hZ : Z ∈ F) (hX' : X' ∈ F) (hL : ∀ Y ∈ L, Y ∈ F) : cell Z X' L S ∈ F := by
  classical
  have : cell Z X' L S = (Z \ X') ∩ ⋂ Y ∈ L, (if Y ∈ S then Y else Yᶜ) := by
    ext y
    simp only [cell, mem_ofPred_eq, mem_inter_iff, mem_sdiff, mem_iInter, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun Y _ => ?_
    split_ifs with h <;> simp [h]
  rw [this]
  refine hF.inter_mem (hF.diff_mem hZ hX') (hF.biInter_mem L _ fun Y hY => ?_)
  split_ifs
  exacts [hL Y hY, hF.compl_mem _ (hL Y hY)]

/-- A point of a cell in the closure of another cell has the same pattern. -/
theorem pattern_of_closure {Z X' : Set X} {L S T : Finset (Set X)} {x : X}
    (hX' : ∀ Y ∈ L, bd Z (Y ∩ Z) ⊆ X') (hx : x ∈ cell Z X' L S)
    (hxT : x ∈ closure (cell Z X' L T)) : ∀ Y ∈ L, Y ∈ S ↔ Y ∈ T := by
  intro Y hY
  have hb : x ∉ bd Z (Y ∩ Z) := fun h => hx.2.1 (hX' Y hY h)
  rw [bd, sdiff_inter_self_eq_sdiff] at hb
  by_cases hxY : x ∈ Y
  · have hS : Y ∈ S := (hx.2.2 Y hY).1 hxY
    refine ⟨fun _ => ?_, fun _ => hS⟩
    by_contra hT
    exact hb ⟨subset_closure ⟨hxY, hx.1⟩, closure_mono (t := Z \ Y)
      (fun y hy => ⟨hy.1, fun h => hT ((hy.2.2 Y hY).1 h)⟩) hxT⟩
  · have hS : Y ∉ S := fun h => hxY ((hx.2.2 Y hY).2 h)
    refine ⟨fun h => absurd h hS, fun hT => ?_⟩
    exact (hb ⟨closure_mono (t := Y ∩ Z) (fun y hy => ⟨(hy.2.2 Y hY).2 hT, hy.1⟩) hxT,
      subset_closure ⟨hx.1, hxY⟩⟩).elim

omit [TopologicalSpace X] in
theorem eq_of_pattern {L S T : Finset (Set X)} (hS : S ⊆ L) (hT : T ⊆ L)
    (h : ∀ Y ∈ L, Y ∈ S ↔ Y ∈ T) : S = T :=
  Finset.ext fun Y => ⟨fun hY => (h Y (hS hY)).1 hY, fun hY => (h Y (hT hY)).2 hY⟩

omit [TopologicalSpace X] in
theorem mem_cell_filter {Z X' : Set X}
    {L : Finset (Set X)} {y : X} [DecidablePred fun Y : Set X => y ∈ Y] (hy : y ∈ Z)
    (hy' : y ∉ X') :
    y ∈ cell Z X' L (L.filter (fun Y => y ∈ Y)) :=
  ⟨hy, hy', fun Y hY => by simp [hY]⟩

omit [TopologicalSpace X] in
theorem filter_eq_of_mem_cell {Z X' : Set X} {L S : Finset (Set X)} {y : X}
    [DecidablePred fun Y : Set X => y ∈ Y] (hS : S ⊆ L) (hy : y ∈ cell Z X' L S) :
    L.filter (fun Y => y ∈ Y) = S :=
  eq_of_pattern (Finset.filter_subset _ _) hS fun Y hY => by simp [hY, hy.2.2 Y hY]

omit [TopologicalSpace X] in
/-- A cell of a decomposition compatible with `L`, inside `Z ∖ X'`, lies in the cell of the
pattern of any of its points. -/
theorem subset_cell {Z X' q : Set X} {L : Finset (Set X)} {y : X}
    [DecidablePred fun Y : Set X => y ∈ Y]
    (hc : ∀ Y ∈ L, q ⊆ Y ∨ Disjoint q Y) (hq : q ⊆ Z \ X') (hy : y ∈ q) :
    q ⊆ cell Z X' L (L.filter (fun Y => y ∈ Y)) := by
  intro z hz
  refine ⟨(hq hz).1, (hq hz).2, fun Y hY => ?_⟩
  simp only [Finset.mem_filter, hY, true_and]
  rcases hc Y hY with h | h
  · exact ⟨fun _ => h hy, fun _ => h hz⟩
  · exact ⟨fun h' => absurd h' (h.notMem_of_mem_left hz),
      fun h' => absurd h' (h.notMem_of_mem_left hy)⟩

/-! ### Existence of the coarsest decomposition (page 14) -/

/-- One step of the induction: remove the boundaries of the members of `L`, cut the open
rest by the patterns, and decompose the boundaries by the induction hypothesis. -/
theorem step (hF : Tame F) {Z : Set X} (hZF : Z ∈ F) (hZc : IsClosed Z) (L : Finset (Set X))
    (hL : ∀ Y ∈ L, Y ∈ F)
    (IH : ∀ B, B ∈ F → IsClosed B → B ⊆ Z → Rare B Z → ∀ L' : Finset (Set X),
      (∀ Y ∈ L', Y ∈ F) → ∃ P, Good F L' B P ∧ ∀ Q, Good F L' B Q → Coarser P Q) :
    ∃ P, Good F L Z P ∧ ∀ Q, Good F L Z Q → Coarser P Q := by
  classical
  set X' := ⋃ Y ∈ L, bd Z (Y ∩ Z) with hX'def
  have hbd : ∀ Y ∈ L, bd Z (Y ∩ Z) ⊆ X' := fun Y hY =>
    subset_biUnion_of_mem (u := fun Y => bd Z (Y ∩ Z)) hY
  have hX'F : X' ∈ F :=
    hF.biUnion_mem L _ fun Y hY => hF.bd_mem hZF (hF.inter_mem (hL Y hY) hZF)
  have hX'c : IsClosed X' := isClosed_biUnion_finset fun Y _ => isClosed_bd Z _
  have hX'Z : X' ⊆ Z := iUnion₂_subset fun Y _ =>
    inter_subset_left.trans (closure_minimal inter_subset_right hZc)
  have hX'r : Rare X' Z := rare_biUnion L _ fun Y hY =>
    ⟨hF.rare_bd hZF (hF.inter_mem (hL Y hY) hZF) inter_subset_right, isClosed_bd Z _⟩
  set U := (L.powerset.image (cell Z X' L)).filter (·.Nonempty) with hUdef
  have hU : ∀ c, c ∈ U ↔ (∃ S, S ⊆ L ∧ cell Z X' L S = c) ∧ c.Nonempty := by
    intro c
    simp [hUdef]
  have hUsub : ∀ c ∈ U, c ⊆ Z \ X' := by
    intro c hc
    obtain ⟨⟨S, -, rfl⟩, -⟩ := (hU c).1 hc
    exact fun y hy => ⟨hy.1, hy.2.1⟩
  have hUF : ∀ c ∈ U, c ∈ F := by
    intro c hc
    obtain ⟨⟨S, -, rfl⟩, -⟩ := (hU c).1 hc
    exact hF.cell_mem S hZF hX'F hL
  have hUmem : ∀ y ∈ Z, y ∉ X' → cell Z X' L (L.filter fun Y => y ∈ Y) ∈ U := fun y hy hy' =>
    (hU _).2 ⟨⟨_, Finset.filter_subset _ _, rfl⟩, ⟨y, mem_cell_filter hy hy'⟩⟩
  set L' := L.image (· ∩ X') ∪ U.image (fun u => closure u ∩ X') with hL'def
  have hL'F : ∀ Y ∈ L', Y ∈ F := by
    intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · obtain ⟨Y₀, hY₀, rfl⟩ := Finset.mem_image.1 h
      exact hF.inter_mem (hL Y₀ hY₀) hX'F
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact hF.inter_mem (hF.closure_mem _ (hUF u hu)) hX'F
  have hL'1 : ∀ Y ∈ L, Y ∩ X' ∈ L' := fun Y hY =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hY)
  have hL'2 : ∀ u ∈ U, closure u ∩ X' ∈ L' := fun u hu =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun u => closure u ∩ X') hu)
  obtain ⟨P', ⟨hP', hP'F, hP'c⟩, hP'min⟩ := IH X' hX'F hX'c hX'Z hX'r L' hL'F
  have hP'X : ∀ c ∈ P', c ⊆ X' := fun c hc => hP'.subset hc
  have hcl : ∀ c ∈ P', closure c ⊆ X' := fun c hc => closure_minimal (hP'X c hc) hX'c
  -- two cells of the open part: closure meeting the other forces equality
  have hUU : ∀ c ∈ U, ∀ d ∈ U, (closure c ∩ d).Nonempty → c = d := by
    intro c hc d hd ⟨x, hxc, hxd⟩
    obtain ⟨⟨S, hS, rfl⟩, -⟩ := (hU c).1 hc
    obtain ⟨⟨T, hT, rfl⟩, -⟩ := (hU d).1 hd
    rw [eq_of_pattern hT hS (pattern_of_closure hbd hxd hxc)]
  -- a cell of `P'` and a cell of the open part are disjoint, and so is the closure of the first
  have hPU : ∀ c ∈ P', ∀ d ∈ U, ¬ (closure c ∩ d).Nonempty := by
    rintro c hc d hd ⟨x, hxc, hxd⟩
    exact (hUsub d hd hxd).2 (hcl c hc hxc)
  refine ⟨P' ∪ U, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    exacts [hP'.nonempty c h, ((hU c).1 h).2]
  · intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc <;> rcases Finset.mem_union.1 hd with hd | hd
    · exact hP'.disjoint c hc d hd hcd
    · exact Set.disjoint_left.2 fun x hxc hxd => hPU c hc d hd ⟨x, subset_closure hxc, hxd⟩
    · exact Set.disjoint_right.2 fun x hxd hxc => hPU d hd c hc ⟨x, subset_closure hxd, hxc⟩
    · exact Set.disjoint_left.2 fun x hxc hxd => hcd (hUU c hc d hd ⟨x, subset_closure hxc, hxd⟩)
  · rw [Finset.set_biUnion_union, hP'.cover]
    have : ⋃ c ∈ U, c = Z \ X' := by
      refine Subset.antisymm (iUnion₂_subset hUsub) fun y hy => ?_
      exact mem_biUnion (hUmem y hy.1 hy.2) (mem_cell_filter hy.1 hy.2)
    rw [this, union_sdiff_cancel hX'Z]
  · intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc <;> rcases Finset.mem_union.1 hd with hd | hd
    · exact hP'.frontier c hc d hd hcd
    · exact absurd hcd (hPU c hc d hd)
    · obtain ⟨x, hxc, hxd⟩ := hcd
      rcases hP'c _ (hL'2 c hc) d hd with h | h
      · exact h.trans inter_subset_left
      · exact absurd (Set.disjoint_left.1 h hxd) (fun h' => h' ⟨hxc, hP'X d hd hxd⟩)
    · rw [← hUU c hc d hd hcd]; exact subset_closure
  · intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc <;> rcases Finset.mem_union.1 hd with hd | hd
    · exact hP'.distinct c hc d hd hcd
    · obtain ⟨y, hy⟩ := ((hU d).1 hd).2
      exact absurd ⟨y, hcd ▸ subset_closure hy, hy⟩ (hPU c hc d hd)
    · obtain ⟨y, hy⟩ := ((hU c).1 hc).2
      exact absurd ⟨y, hcd.symm ▸ subset_closure hy, hy⟩ (hPU d hd c hc)
    · obtain ⟨y, hy⟩ := ((hU d).1 hd).2
      exact hUU c hc d hd ⟨y, hcd ▸ subset_closure hy, hy⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    exacts [hP'F c h, hUF c h]
  · intro Y hY c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · rcases hP'c _ (hL'1 Y hY) c hc with h | h
      · exact Or.inl (h.trans inter_subset_left)
      · exact Or.inr (Set.disjoint_left.2 fun x hxc hxY =>
          Set.disjoint_left.1 h hxc ⟨hxY, hP'X c hc hxc⟩)
    · obtain ⟨⟨S, hS, rfl⟩, -⟩ := (hU c).1 hc
      by_cases h : Y ∈ S
      · exact Or.inl fun y hy => (hy.2.2 Y hY).2 h
      · exact Or.inr (Set.disjoint_left.2 fun y hy hyY => h ((hy.2.2 Y hY).1 hyY))
  -- the decomposition is the coarsest
  rintro Q ⟨hQ, hQF, hQc⟩ q hq
  have hdich : ∀ c ∈ Q, c ⊆ X' ∨ c ⊆ Z \ X' := by
    intro c hc
    by_cases hm : (c ∩ X').Nonempty
    · obtain ⟨x, hxc, hxX⟩ := hm
      obtain ⟨Y, hY, hxb⟩ := mem_iUnion₂.1 hxX
      exact Or.inl ((subset_bd hQ (fun c hc => hQc Y hY c hc) hc ⟨x, hxc, hxb⟩).trans (hbd Y hY))
    · exact Or.inr fun y hy => ⟨hQ.subset hc hy, fun hyX => hm ⟨y, hy, hyX⟩⟩
  rcases hdich q hq with hqX | hqU
  · set Q' := Q.filter (· ⊆ X') with hQ'def
    have hQ'Q : Q' ⊆ Q := Finset.filter_subset _ _
    have hQ' : Good F L' X' Q' := by
      refine ⟨⟨fun c hc => hQ.nonempty c (hQ'Q hc),
        fun c hc d hd => hQ.disjoint c (hQ'Q hc) d (hQ'Q hd), ?_,
        fun c hc d hd => hQ.frontier c (hQ'Q hc) d (hQ'Q hd),
        fun c hc d hd => hQ.distinct c (hQ'Q hc) d (hQ'Q hd)⟩,
        fun c hc => hQF c (hQ'Q hc), ?_⟩
      · refine Subset.antisymm (iUnion₂_subset fun c hc => (Finset.mem_filter.1 hc).2)
          fun x hx => ?_
        obtain ⟨c, hc, hxc⟩ := hQ.exists_mem (hX'Z hx)
        rcases hdich c hc with h | h
        · exact mem_biUnion (Finset.mem_filter.2 ⟨hc, h⟩) hxc
        · exact absurd hx (h hxc).2
      · intro Y' hY' c hc
        have hcX := (Finset.mem_filter.1 hc).2
        rcases Finset.mem_union.1 hY' with h | h
        · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 h
          rcases hQc Y hY c (hQ'Q hc) with h' | h'
          · exact Or.inl (subset_inter h' hcX)
          · exact Or.inr (h'.mono_right inter_subset_left)
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
          by_cases hm : (closure u ∩ c).Nonempty
          · left
            refine subset_inter ?_ hcX
            have hu' : u ⊆ ⋃ s ∈ Q.filter (· ⊆ u), s := by
              intro y hy
              obtain ⟨⟨S, hS, rfl⟩, -⟩ := (hU _).1 hu
              obtain ⟨d, hd, hyd⟩ := hQ.exists_mem hy.1
              have hdU : d ⊆ Z \ X' := (hdich d hd).resolve_left fun h => hy.2.1 (h hyd)
              have := subset_cell (fun Y hY => hQc Y hY d hd) hdU hyd
              rw [filter_eq_of_mem_cell hS hy] at this
              exact mem_biUnion (Finset.mem_filter.2 ⟨hd, this⟩) hyd
            obtain ⟨s, hs, hcs⟩ := hQ.of_closure (Finset.filter_subset _ _) (hQ'Q hc)
              (hm.mono (inter_subset_inter_left _ (closure_mono hu')))
            exact hcs.trans (closure_mono (Finset.mem_filter.1 hs).2)
          · exact Or.inr (Set.disjoint_left.2 fun x hxc hx => hm ⟨x, hx.1, hxc⟩)
    obtain ⟨p, hp, hqp⟩ := hP'min Q' hQ' q (Finset.mem_filter.2 ⟨hq, hqX⟩)
    exact ⟨p, Finset.mem_union_left _ hp, hqp⟩
  · obtain ⟨y, hy⟩ := hQ.nonempty q hq
    exact ⟨_, Finset.mem_union_right _ (hUmem y (hqU hy).1 (hqU hy).2),
      subset_cell (fun Y hY => hQc Y hY q hq) hqU hy⟩

/-- Induction on condition e): the statement of page 14 on every closed member. -/
theorem exists_coarsest (hF : Tame F) {Z : Set X} (hZF : Z ∈ F) (hZc : IsClosed Z)
    (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, Good F L Z P ∧ ∀ Q, Good F L Z Q → Coarser P Q := by
  let R : Set X → Set X → Prop := fun B Z =>
    (Z.Nonempty ∧ Z ∈ F ∧ IsClosed Z) ∧ (B ∈ F ∧ IsClosed B ∧ B ⊆ Z ∧ Rare B Z)
  have hwf : WellFounded R := wellFounded_iff_isEmpty_descending_chain.2 ⟨fun ⟨f, hf⟩ => by
    obtain ⟨n, hn⟩ := hF.dcc f (fun n => ⟨(hf n).1.2.1, (hf n).1.2.2⟩)
      (fun n => ⟨(hf n).2.2.2.1, (hf n).2.2.2.2⟩)
    exact (hf n).1.1.ne_empty hn⟩
  induction Z using hwf.induction generalizing L with
  | _ Z ih =>
    rcases Z.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, ⟨⟨by simp, by simp, by simp, by simp, by simp⟩, by simp, by simp [Compat]⟩,
        fun Q hQ q hq => ?_⟩
      obtain ⟨x, hx⟩ := hQ.1.nonempty q hq
      exact (hQ.1.subset hq hx).elim
    · exact step hF hZF hZc L hL fun B hBF hBc hBZ hBr L' hL' =>
        ih B ⟨⟨hne, hZF, hZc⟩, hBF, hBc, hBZ, hBr⟩ hBF hBc L' hL'

/-- **Page 14.** Under a) to e), for every finite family `L ⊂ F` there is an `F`-admissible
cellular decomposition of `X` of which the members of `L` are unions of cells, and among them
one coarser than all the others. -/
theorem page14 (hF : Tame F) (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, Good F L univ P ∧ ∀ Q, Good F L univ Q → Coarser P Q :=
  exists_coarsest hF hF.univ_mem isClosed_univ L hL

end Grothendieck.Folder121

/-!
### Connected cells (page 16, condition f))

Condition f) of page 9: a locally closed member `B ∖ C` (`B`, `C` closed members) has finitely
many connected components, all in `F`. The remark of page 16: under a) to f), the proposition of
page 14 holds with connected cells, the coarsest being taken among the decompositions with
connected cells (`page16`, by `exists_coarsest_conn` on every closed member). The open cells of
the induction step are replaced by their connected components; a component `V` of an open cell
`U` satisfies `V̄ ∩ U ⊆ V`, which gives the frontier condition, and a connected cell of a
competing decomposition lying in `U` lies in one component, which gives « la plus grossière ».
-/

namespace Grothendieck.Folder121

open Set

variable {X : Type*} [TopologicalSpace X] {F : Set (Set X)}

/-- Condition f) (page 9): a locally closed member has finitely many connected components, all
of them members. -/
def CondF (F : Set (Set X)) : Prop :=
  ∀ B ∈ F, ∀ C ∈ F, IsClosed B → IsClosed C →
    (connectedComponentIn (B \ C) '' (B \ C)).Finite ∧
      ∀ x ∈ B \ C, connectedComponentIn (B \ C) x ∈ F

/-- A good decomposition with connected cells. -/
def GoodC (F : Set (Set X)) (L : Finset (Set X)) (Z : Set X) (P : Finset (Set X)) : Prop :=
  Good F L Z P ∧ ∀ c ∈ P, IsConnected c

/-- One step of the induction with connected cells. -/
theorem step_conn (hF : Tame F) (hf : CondF F) {Z : Set X} (hZF : Z ∈ F) (hZc : IsClosed Z)
    (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F)
    (IH : ∀ B, B ∈ F → IsClosed B → B ⊆ Z → Rare B Z → ∀ L' : Finset (Set X),
      (∀ Y ∈ L', Y ∈ F) → ∃ P, GoodC F L' B P ∧ ∀ Q, GoodC F L' B Q → Coarser P Q) :
    ∃ P, GoodC F L Z P ∧ ∀ Q, GoodC F L Z Q → Coarser P Q := by
  classical
  set X' := ⋃ Y ∈ L, bd Z (Y ∩ Z)
  have hbd : ∀ Y ∈ L, bd Z (Y ∩ Z) ⊆ X' := fun Y hY =>
    subset_biUnion_of_mem (u := fun Y => bd Z (Y ∩ Z)) hY
  have hX'F : X' ∈ F :=
    hF.biUnion_mem L _ fun Y hY => hF.bd_mem hZF (hF.inter_mem (hL Y hY) hZF)
  have hX'c : IsClosed X' := isClosed_biUnion_finset fun Y _ => isClosed_bd Z _
  have hX'Z : X' ⊆ Z := iUnion₂_subset fun Y _ =>
    inter_subset_left.trans (closure_minimal inter_subset_right hZc)
  have hX'r : Rare X' Z := rare_biUnion L _ fun Y hY =>
    ⟨hF.rare_bd hZF (hF.inter_mem (hL Y hY) hZF) inter_subset_right, isClosed_bd Z _⟩
  set U := (L.powerset.image (cell Z X' L)).filter (·.Nonempty)
  have hU : ∀ c, c ∈ U ↔ (∃ S, S ⊆ L ∧ cell Z X' L S = c) ∧ c.Nonempty := by simp [U]
  have hUsub : ∀ c ∈ U, c ⊆ Z \ X' := by
    intro c hc
    obtain ⟨⟨S, -, rfl⟩, -⟩ := (hU c).1 hc
    exact fun y hy => ⟨hy.1, hy.2.1⟩
  have hUmem : ∀ y ∈ Z, y ∉ X' → cell Z X' L (L.filter fun Y => y ∈ Y) ∈ U := fun y hy hy' =>
    (hU _).2 ⟨⟨_, Finset.filter_subset _ _, rfl⟩, ⟨y, mem_cell_filter hy hy'⟩⟩
  have hUU : ∀ c ∈ U, ∀ d ∈ U, (closure c ∩ d).Nonempty → c = d := by
    intro c hc d hd ⟨x, hxc, hxd⟩
    obtain ⟨⟨S, hS, rfl⟩, -⟩ := (hU c).1 hc
    obtain ⟨⟨T, hT, rfl⟩, -⟩ := (hU d).1 hd
    rw [eq_of_pattern hT hS (pattern_of_closure hbd hxd hxc)]
  -- an open cell is locally closed, so condition f) applies to it
  have hloc : ∀ u ∈ U, closure u \ X' = u := by
    intro u hu
    refine Subset.antisymm (fun y ⟨hy, hyX⟩ => ?_) fun y hy =>
      ⟨subset_closure hy, (hUsub u hu hy).2⟩
    have hyZ : y ∈ Z := closure_minimal (fun z hz => (hUsub u hu hz).1) hZc hy
    rw [hUU u hu _ (hUmem y hyZ hyX) ⟨y, hy, mem_cell_filter hyZ hyX⟩]
    exact mem_cell_filter hyZ hyX
  have hfu : ∀ u ∈ U, (connectedComponentIn u '' u).Finite ∧
      ∀ x ∈ u, connectedComponentIn u x ∈ F := fun u hu => by
    obtain ⟨S, -, rfl⟩ := ((hU u).1 hu).1
    have := hf _ (hF.closure_mem _ (hF.cell_mem S hZF hX'F hL)) _ hX'F isClosed_closure hX'c
    rwa [hloc _ hu] at this
  -- the connected components of the open cells
  set W := (U.finite_toSet.biUnion fun u hu => (hfu u hu).1).toFinset
  have hW : ∀ c, c ∈ W ↔ ∃ u ∈ U, ∃ x ∈ u, connectedComponentIn u x = c := by simp [W]
  have hWcl : ∀ u ∈ U, ∀ x ∈ u, closure (connectedComponentIn u x) ∩ u ⊆
      connectedComponentIn u x := fun u _ x hx =>
    (isPreconnected_connectedComponentIn.subset_closure
      (subset_inter subset_closure (connectedComponentIn_subset _ _)) inter_subset_left)
      |>.subset_connectedComponentIn ⟨subset_closure (mem_connectedComponentIn hx),
        hx⟩ inter_subset_right |>.trans (connectedComponentIn_eq
          (mem_connectedComponentIn hx)).symm.subset
  have hWsub : ∀ c ∈ W, c ⊆ Z \ X' := by
    intro c hc
    obtain ⟨u, hu, x, -, rfl⟩ := (hW c).1 hc
    exact (connectedComponentIn_subset _ _).trans (hUsub u hu)
  have hWF : ∀ c ∈ W, c ∈ F := by
    intro c hc
    obtain ⟨u, hu, x, hx, rfl⟩ := (hW c).1 hc
    exact (hfu u hu).2 x hx
  have hWconn : ∀ c ∈ W, IsConnected c := by
    intro c hc
    obtain ⟨u, -, x, hx, rfl⟩ := (hW c).1 hc
    exact isConnected_connectedComponentIn_iff.2 hx
  have hWmem : ∀ y ∈ Z, y ∉ X' →
      connectedComponentIn (cell Z X' L (L.filter fun Y => y ∈ Y)) y ∈ W := fun y hy hy' =>
    (hW _).2 ⟨_, hUmem y hy hy', y, mem_cell_filter hy hy', rfl⟩
  have hWW : ∀ c ∈ W, ∀ d ∈ W, (closure c ∩ d).Nonempty → c = d := by
    intro c hc d hd ⟨z, hzc, hzd⟩
    obtain ⟨u, hu, x, hx, rfl⟩ := (hW c).1 hc
    obtain ⟨v, hv, y, hy, rfl⟩ := (hW d).1 hd
    obtain rfl := hUU u hu v hv
      ⟨z, closure_mono (connectedComponentIn_subset _ _) hzc, connectedComponentIn_subset _ _ hzd⟩
    rw [connectedComponentIn_eq (hWcl u hu x hx ⟨hzc, connectedComponentIn_subset _ _ hzd⟩),
      connectedComponentIn_eq hzd]
  set L' := L.image (· ∩ X') ∪ W.image (fun u => closure u ∩ X')
  have hL'F : ∀ Y ∈ L', Y ∈ F := by
    intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · obtain ⟨Y₀, hY₀, rfl⟩ := Finset.mem_image.1 h
      exact hF.inter_mem (hL Y₀ hY₀) hX'F
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      exact hF.inter_mem (hF.closure_mem _ (hWF u hu)) hX'F
  have hL'1 : ∀ Y ∈ L, Y ∩ X' ∈ L' := fun Y hY =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hY)
  have hL'2 : ∀ u ∈ W, closure u ∩ X' ∈ L' := fun u hu =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun u => closure u ∩ X') hu)
  obtain ⟨P', ⟨⟨hP', hP'F, hP'c⟩, hP'conn⟩, hP'min⟩ := IH X' hX'F hX'c hX'Z hX'r L' hL'F
  have hP'X : ∀ c ∈ P', c ⊆ X' := fun c hc => hP'.subset hc
  have hcl : ∀ c ∈ P', closure c ⊆ X' := fun c hc => closure_minimal (hP'X c hc) hX'c
  have hPU : ∀ c ∈ P', ∀ d ∈ W, ¬ (closure c ∩ d).Nonempty := by
    rintro c hc d hd ⟨x, hxc, hxd⟩
    exact (hWsub d hd hxd).2 (hcl c hc hxc)
  refine ⟨P' ∪ W, ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    exacts [hP'.nonempty c h, (hWconn c h).1]
  · intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc <;> rcases Finset.mem_union.1 hd with hd | hd
    · exact hP'.disjoint c hc d hd hcd
    · exact Set.disjoint_left.2 fun x hxc hxd => hPU c hc d hd ⟨x, subset_closure hxc, hxd⟩
    · exact Set.disjoint_right.2 fun x hxd hxc => hPU d hd c hc ⟨x, subset_closure hxd, hxc⟩
    · exact Set.disjoint_left.2 fun x hxc hxd => hcd (hWW c hc d hd ⟨x, subset_closure hxc, hxd⟩)
  · rw [Finset.set_biUnion_union, hP'.cover]
    have : ⋃ c ∈ W, c = Z \ X' := by
      refine Subset.antisymm (iUnion₂_subset hWsub) fun y hy => ?_
      exact mem_biUnion (hWmem y hy.1 hy.2) (mem_connectedComponentIn (mem_cell_filter hy.1 hy.2))
    rw [this, union_sdiff_cancel hX'Z]
  · intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc <;> rcases Finset.mem_union.1 hd with hd | hd
    · exact hP'.frontier c hc d hd hcd
    · exact absurd hcd (hPU c hc d hd)
    · obtain ⟨x, hxc, hxd⟩ := hcd
      rcases hP'c _ (hL'2 c hc) d hd with h | h
      · exact h.trans inter_subset_left
      · exact absurd (Set.disjoint_left.1 h hxd) (fun h' => h' ⟨hxc, hP'X d hd hxd⟩)
    · rw [← hWW c hc d hd hcd]; exact subset_closure
  · intro c hc d hd hcd
    rcases Finset.mem_union.1 hc with hc | hc <;> rcases Finset.mem_union.1 hd with hd | hd
    · exact hP'.distinct c hc d hd hcd
    · obtain ⟨y, hy⟩ := (hWconn d hd).1
      exact absurd ⟨y, hcd ▸ subset_closure hy, hy⟩ (hPU c hc d hd)
    · obtain ⟨y, hy⟩ := (hWconn c hc).1
      exact absurd ⟨y, hcd.symm ▸ subset_closure hy, hy⟩ (hPU d hd c hc)
    · obtain ⟨y, hy⟩ := (hWconn d hd).1
      exact hWW c hc d hd ⟨y, hcd ▸ subset_closure hy, hy⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    exacts [hP'F c h, hWF c h]
  · intro Y hY c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · rcases hP'c _ (hL'1 Y hY) c hc with h | h
      · exact Or.inl (h.trans inter_subset_left)
      · exact Or.inr (Set.disjoint_left.2 fun x hxc hxY =>
          Set.disjoint_left.1 h hxc ⟨hxY, hP'X c hc hxc⟩)
    · obtain ⟨u, hu, x, -, rfl⟩ := (hW c).1 hc
      obtain ⟨⟨S, hS, rfl⟩, -⟩ := (hU u).1 hu
      by_cases h : Y ∈ S
      · exact Or.inl fun y hy => ((connectedComponentIn_subset _ _ hy).2.2 Y hY).2 h
      · exact Or.inr (Set.disjoint_left.2 fun y hy hyY =>
          h (((connectedComponentIn_subset _ _ hy).2.2 Y hY).1 hyY))
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    exacts [hP'conn c h, hWconn c h]
  -- the decomposition is the coarsest
  rintro Q ⟨⟨hQ, hQF, hQc⟩, hQconn⟩ q hq
  have hdich : ∀ c ∈ Q, c ⊆ X' ∨ c ⊆ Z \ X' := by
    intro c hc
    by_cases hm : (c ∩ X').Nonempty
    · obtain ⟨x, hxc, hxX⟩ := hm
      obtain ⟨Y, hY, hxb⟩ := mem_iUnion₂.1 hxX
      exact Or.inl ((subset_bd hQ (fun c hc => hQc Y hY c hc) hc ⟨x, hxc, hxb⟩).trans (hbd Y hY))
    · exact Or.inr fun y hy => ⟨hQ.subset hc hy, fun hyX => hm ⟨y, hy, hyX⟩⟩
  -- a cell of `Q` in the open part lies in the component of any of its points
  have hQW : ∀ d ∈ Q, d ⊆ Z \ X' → ∀ y ∈ d,
      d ⊆ connectedComponentIn (cell Z X' L (L.filter fun Y => y ∈ Y)) y := fun d hd hdU y hy =>
    (hQconn d hd).2.subset_connectedComponentIn hy
      (subset_cell (fun Y hY => hQc Y hY d hd) hdU hy)
  rcases hdich q hq with hqX | hqU
  · set Q' := Q.filter (· ⊆ X')
    have hQ'Q : Q' ⊆ Q := Finset.filter_subset _ _
    have hQ' : GoodC F L' X' Q' := by
      refine ⟨⟨⟨fun c hc => hQ.nonempty c (hQ'Q hc),
        fun c hc d hd => hQ.disjoint c (hQ'Q hc) d (hQ'Q hd), ?_,
        fun c hc d hd => hQ.frontier c (hQ'Q hc) d (hQ'Q hd),
        fun c hc d hd => hQ.distinct c (hQ'Q hc) d (hQ'Q hd)⟩,
        fun c hc => hQF c (hQ'Q hc), ?_⟩, fun c hc => hQconn c (hQ'Q hc)⟩
      · refine Subset.antisymm (iUnion₂_subset fun c hc => (Finset.mem_filter.1 hc).2)
          fun x hx => ?_
        obtain ⟨c, hc, hxc⟩ := hQ.exists_mem (hX'Z hx)
        rcases hdich c hc with h | h
        · exact mem_biUnion (Finset.mem_filter.2 ⟨hc, h⟩) hxc
        · exact absurd hx (h hxc).2
      · intro Y' hY' c hc
        have hcX := (Finset.mem_filter.1 hc).2
        rcases Finset.mem_union.1 hY' with h | h
        · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 h
          rcases hQc Y hY c (hQ'Q hc) with h' | h'
          · exact Or.inl (subset_inter h' hcX)
          · exact Or.inr (h'.mono_right inter_subset_left)
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 h
          by_cases hm : (closure w ∩ c).Nonempty
          · left
            refine subset_inter ?_ hcX
            have hw' : w ⊆ ⋃ s ∈ Q.filter (· ⊆ w), s := by
              intro y hy
              obtain ⟨u, hu, x, -, rfl⟩ := (hW w).1 hw
              obtain ⟨⟨S, hS, rfl⟩, -⟩ := (hU u).1 hu
              have hyu := connectedComponentIn_subset _ _ hy
              obtain ⟨d, hd, hyd⟩ := hQ.exists_mem hyu.1
              have hdU : d ⊆ Z \ X' := (hdich d hd).resolve_left fun h => hyu.2.1 (h hyd)
              have := hQW d hd hdU y hyd
              rw [filter_eq_of_mem_cell hS hyu, ← connectedComponentIn_eq hy] at this
              exact mem_biUnion (Finset.mem_filter.2 ⟨hd, this⟩) hyd
            obtain ⟨s, hs, hcs⟩ := hQ.of_closure (Finset.filter_subset _ _) (hQ'Q hc)
              (hm.mono (inter_subset_inter_left _ (closure_mono hw')))
            exact hcs.trans (closure_mono (Finset.mem_filter.1 hs).2)
          · exact Or.inr (Set.disjoint_left.2 fun x hxc hx => hm ⟨x, hx.1, hxc⟩)
    obtain ⟨p, hp, hqp⟩ := hP'min Q' hQ' q (Finset.mem_filter.2 ⟨hq, hqX⟩)
    exact ⟨p, Finset.mem_union_left _ hp, hqp⟩
  · obtain ⟨y, hy⟩ := hQ.nonempty q hq
    exact ⟨_, Finset.mem_union_right _ (hWmem y (hqU hy).1 (hqU hy).2), hQW q hq hqU y hy⟩

/-- Induction on condition e), with connected cells, on every closed member. -/
theorem exists_coarsest_conn (hF : Tame F) (hf : CondF F) {Z : Set X} (hZF : Z ∈ F)
    (hZc : IsClosed Z) (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, GoodC F L Z P ∧ ∀ Q, GoodC F L Z Q → Coarser P Q := by
  let R : Set X → Set X → Prop := fun B Z =>
    (Z.Nonempty ∧ Z ∈ F ∧ IsClosed Z) ∧ (B ∈ F ∧ IsClosed B ∧ B ⊆ Z ∧ Rare B Z)
  have hwf : WellFounded R := wellFounded_iff_isEmpty_descending_chain.2 ⟨fun ⟨f, hf⟩ => by
    obtain ⟨n, hn⟩ := hF.dcc f (fun n => ⟨(hf n).1.2.1, (hf n).1.2.2⟩)
      (fun n => ⟨(hf n).2.2.2.1, (hf n).2.2.2.2⟩)
    exact (hf n).1.1.ne_empty hn⟩
  induction Z using hwf.induction generalizing L with
  | _ Z ih =>
    rcases Z.eq_empty_or_nonempty with rfl | hne
    · refine ⟨∅, ⟨⟨⟨by simp, by simp, by simp, by simp, by simp⟩, by simp, by simp [Compat]⟩,
        by simp⟩, fun Q hQ q hq => ?_⟩
      obtain ⟨x, hx⟩ := hQ.1.1.nonempty q hq
      exact (hQ.1.1.subset hq hx).elim
    · exact step_conn hF hf hZF hZc L hL fun B hBF hBc hBZ hBr L' hL' =>
        ih B ⟨⟨hne, hZF, hZc⟩, hBF, hBc, hBZ, hBr⟩ hBF hBc L' hL'

/-- **Page 16.** Under a) to f), for every finite family `L ⊂ F` there is an `F`-admissible
cellular decomposition of `X` with connected cells of which the members of `L` are unions of
cells, and among them one coarser than all the others. -/
theorem page16 (hF : Tame F) (hf : CondF F) (L : Finset (Set X)) (hL : ∀ Y ∈ L, Y ∈ F) :
    ∃ P, GoodC F L univ P ∧ ∀ Q, GoodC F L univ Q → Coarser P Q :=
  exists_coarsest_conn hF hf hF.univ_mem isClosed_univ L hL

end Grothendieck.Folder121
