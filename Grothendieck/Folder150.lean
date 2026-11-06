module

public import Mathlib

@[expose] public section


/-!
# Folder 150, page 19: without `Xᵢ ∩ Y = f(Ẋᵢ)`, the reconstruction is not faithful

Page 19 of folder 150 (transcription `transcripts/150/batch-01.fr.tex`) states that the systems
`(X, Y, (Xᵢ), T)`, `T` a conic neighbourhood of `Y` in `X` compatible with the closed `Xᵢ`,
are equivalent — morphisms the isomorphisms — to the systems `(X*, Ẋ, (Xᵢ*), Y, f : Ẋ → Y)`,
where `X* = X ∖ T°`, `Ẋ = Ṫ`, `Xᵢ* = Xᵢ ∩ X*` and `f` is `t ↦ 0 · t`. The modernised reading
`transcripts/150/150.modern.tex` (footnote to the Proposition of page 19) objects that the trace
`Xᵢ ∩ Y` is not recovered from the right-hand data, and gives the edition's counterexample
on `[0, 1]`: `Y = {0}`, `T = [0, 1/2]`, and `X₁ = {0}`, `X₁ = ∅`. The reading therefore puts into
« strictement compatible » the condition `Xᵢ ∩ Y = f(Ẋᵢ)`, `Ẋᵢ = Xᵢ ∩ Ṫ` (the conic part
`Xᵢ ∩ T` is *strict*, the circled `T' ∩ Y = 0 · Ṫ'` of page 16).

What is modelled. Everything is the concrete example, inside `ℝ`: `X = [0, 1]`, `Y = {0}`,
`T = [0, 1/2]` with the action `(λ, t) ↦ λ t` of `I = [0, 1]`, `Ṫ = {1/2}`, `X* = [1/2, 1]`,
and the collar `E = [1/2, 3/4] ≃ Ṫ × [0, 1]`, `(1/2, s) ↦ 1/2 + s/4`. A part `C ⊂ T` is conic
when `C = I · (C ∩ Ṫ) ∪ (C ∩ Y)` (the NB of page 15, which contains stability under `I`).
* `isConic_T`, `T_eq_half_smul`: `T` is conic, and strict (`T = ½ · X`);
* `compatible_not_determined` (the edition's counterexample): `{0}` and `∅` are both compatible
  with `T` and with the collar, have the same trace on `X*`, and `{0}` is nonempty — so no
  isomorphism of systems relates them, while their right-hand data coincide;
* `not_strictlyCompatible_singleton_zero`: `{0}` fails `X₁ ∩ Y = f(Ẋ₁)`;
* `eq_of_strictlyCompatible`: with that condition, `X₁` is determined by `X₁ ∩ X*`.

Not formalised: the categories of page 19 and the functor `X = X* ⊔_Ẋ 𝒞(f)` for general
spaces, transversality and equisingularity; only this example is treated.
-/

open Set

namespace Grothendieck.Folder150

/-- The space `X = [0, 1]`. -/
def X : Set ℝ := Icc 0 1

/-- The closed part `Y = {0}`. -/
def Y : Set ℝ := {0}

/-- The conic neighbourhood `T = [0, 1/2]` of `Y`, for the action `(λ, t) ↦ λ t`. -/
def T : Set ℝ := Icc 0 (1 / 2)

/-- Its boundary `Ṫ = {1/2}`. -/
def Tdot : Set ℝ := {1 / 2}

/-- `X* = X ∖ T° = [1/2, 1]`. -/
def Xstar : Set ℝ := Icc (1 / 2) 1

/-- The cone `I · S = {λ s | λ ∈ [0, 1], s ∈ S}`. -/
def cone (S : Set ℝ) : Set ℝ := (fun p : ℝ × ℝ => p.1 * p.2) '' (Icc 0 1 ×ˢ S)

/-- `C ⊂ T` is conic: `C = I · (C ∩ Ṫ) ∪ (C ∩ Y)` (page 15). -/
def IsConic (C : Set ℝ) : Prop := C ⊆ T ∧ C = cone (C ∩ Tdot) ∪ (C ∩ Y)

/-- `T` is compatible with the closed part `X₁ ⊂ X`: `X₁ ∩ T` is conic. -/
def IsCompatible (X₁ : Set ℝ) : Prop := IsClosed X₁ ∧ X₁ ⊆ X ∧ IsConic (X₁ ∩ T)

/-- `X₁` is compatible with the collar `E = [1/2, 3/4] ≃ Ṫ × [0, 1]`: `X₁ ∩ E = X₁₀ × [0, 1]`
with `X₁₀ = X₁ ∩ Ṫ`. -/
def IsCollarCompatible (X₁ : Set ℝ) : Prop :=
  X₁ ∩ Icc (1 / 2) (3 / 4) = (fun p : ℝ × ℝ => p.1 + p.2 / 4) '' ((X₁ ∩ Tdot) ×ˢ Icc 0 1)

/-- Strict compatibility as the reading defines it: compatible, compatible with the collar,
and `X₁ ∩ Y = f(Ẋ₁)` with `f t = 0 · t` and `Ẋ₁ = X₁ ∩ Ṫ`. -/
def IsStrictlyCompatible (X₁ : Set ℝ) : Prop :=
  IsCompatible X₁ ∧ IsCollarCompatible X₁ ∧ X₁ ∩ Y = (fun t : ℝ => 0 * t) '' (X₁ ∩ Tdot)

lemma cone_half : cone Tdot = T := by
  ext x
  simp only [cone, Tdot, T, mem_image, mem_prod, mem_Icc, mem_singleton_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨h0, h1⟩, rfl⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    exact ⟨2 * x, 1 / 2, ⟨⟨by linarith, by linarith⟩, rfl⟩, by ring⟩

theorem isConic_T : IsConic T := ⟨subset_rfl, by
  rw [(inter_eq_right.2 (by norm_num [Tdot, T]) : T ∩ Tdot = Tdot), cone_half,
    union_eq_left.2 inter_subset_left]⟩

/-- `T` is strict: `T = ½ · X`, with `X = [0, 1]` itself conic for the same action. -/
theorem T_eq_half_smul : T = (fun t => 1 / 2 * t) '' X := by
  ext x
  simp only [T, X, mem_image, mem_Icc]
  exact ⟨fun ⟨h0, h1⟩ => ⟨2 * x, ⟨by linarith, by linarith⟩, by ring⟩,
    by rintro ⟨t, ⟨h0, h1⟩, rfl⟩; constructor <;> linarith⟩

/-- A conic part of `T` is `T` if it contains `1/2`, and lies in `Y` otherwise. -/
lemma IsConic.cases {C : Set ℝ} (h : IsConic C) :
    ((1 / 2 : ℝ) ∈ C → C = T) ∧ ((1 / 2 : ℝ) ∉ C → C ⊆ Y) := by
  refine ⟨fun hc => h.1.antisymm ?_, fun hc => ?_⟩
  · rw [h.2, (inter_eq_right.2 (singleton_subset_iff.2 hc) : C ∩ Tdot = Tdot), cone_half]
    exact subset_union_left
  · rw [h.2, Tdot, inter_singleton_eq_empty.2 hc]
    simp [cone]

/-- The edition's counterexample (reading, footnote to page 19): `X₁ = {0}` and `X₁ = ∅` are
both compatible with `T` and with the collar, and have the same trace on `X*` — the same
right-hand data `(X*, Ṫ, X₁*, Y, f)` — but `{0}` is nonempty and `∅` is not, so no
isomorphism of systems takes one to the other. -/
theorem compatible_not_determined :
    IsCompatible {0} ∧ IsCompatible ∅ ∧ IsCollarCompatible {0} ∧ IsCollarCompatible ∅ ∧
      ({0} : Set ℝ) ∩ Xstar = ∅ ∩ Xstar ∧ ({0} : Set ℝ).Nonempty := by
  have h0 : ({0} : Set ℝ) ∩ Tdot = ∅ := by norm_num [Tdot]
  refine ⟨⟨isClosed_singleton, by norm_num [X], ?_, ?_⟩, ⟨isClosed_empty, empty_subset _,
    by simp [IsConic, cone]⟩, ?_, by simp [IsCollarCompatible], ?_, singleton_nonempty 0⟩
  · norm_num [T]
  · rw [show ({0} : Set ℝ) ∩ T = {0} by norm_num [T], h0]
    simp [cone, Y]
  · rw [IsCollarCompatible, h0]
    norm_num
  · norm_num [Xstar]

/-- `{0}` is not strictly compatible: `{0} ∩ Y = {0}`, while `Ẋ₁ = ∅`. -/
theorem not_strictlyCompatible_singleton_zero : ¬ IsStrictlyCompatible {0} := by
  rintro ⟨-, -, h⟩
  rw [show ({0} : Set ℝ) ∩ Tdot = ∅ by norm_num [Tdot], image_empty] at h
  simp [Y] at h

open Classical in
/-- Under strict compatibility, `X₁ ∩ T` is `T` or `∅` according as `1/2 ∈ X₁`. -/
lemma IsStrictlyCompatible.inter_T {X₁ : Set ℝ} (h : IsStrictlyCompatible X₁) :
    X₁ ∩ T = if (1 / 2 : ℝ) ∈ X₁ then T else ∅ := by
  have hc := h.1.2.2.cases
  split_ifs with h2
  · exact hc.1 ⟨h2, by norm_num [T]⟩
  · have hY : X₁ ∩ Y = ∅ := by rw [h.2.2, Tdot, inter_singleton_eq_empty.2 h2, image_empty]
    exact subset_empty_iff.1 fun x hx => hY ▸ ⟨hx.1, hc.2 (fun h' => h2 h'.1) hx⟩

/-- With `X₁ ∩ Y = f(Ẋ₁)`, a strictly compatible `X₁` is determined by its trace on `X*`. -/
theorem eq_of_strictlyCompatible {X₁ X₂ : Set ℝ} (h₁ : IsStrictlyCompatible X₁)
    (h₂ : IsStrictlyCompatible X₂) (h : X₁ ∩ Xstar = X₂ ∩ Xstar) : X₁ = X₂ := by
  have split : ∀ Z : Set ℝ, Z ⊆ X → Z = Z ∩ T ∪ Z ∩ Xstar := fun Z hZ => by
    rw [← inter_union_distrib_left, eq_comm, inter_eq_left]
    refine hZ.trans fun x ⟨h0, h1⟩ => ?_
    by_cases hx : x ≤ 1 / 2
    exacts [Or.inl ⟨h0, hx⟩, Or.inr ⟨by linarith, h1⟩]
  have hm : (1 / 2 : ℝ) ∈ Xstar := by norm_num [Xstar]
  have half : (1 / 2 : ℝ) ∈ X₁ ↔ (1 / 2 : ℝ) ∈ X₂ := ⟨fun a => ((Set.ext_iff.1 h _).1 ⟨a, hm⟩).1,
    fun a => ((Set.ext_iff.1 h _).2 ⟨a, hm⟩).1⟩
  rw [split X₁ h₁.1.2.1, split X₂ h₂.1.2.1, h₁.inter_T, h₂.inter_T, h, half]

end Grothendieck.Folder150

/-!
## Pages 45–47: the combinatorial criterion of the flag fibrations

Pages 45–47 (the modernised reading, end of paragraph 10) state that, `d = (i_1, …, i_p)` an
initial segment of the flag `d' = (i_1, …, i_n)`, the boundary of the fibres of
`Σ_{d'} → Σ_d` is stratified by the `Σ_e`, `e ⊋ d'` a flag with the same terms as `d'` up to
`i_p` and the same last term `i_n`, that these `e` are the non-empty flags of the ordinal sum
`I_{]i_p,i_{p+1}[} ⊔ … ⊔ I_{]i_{n-1},i_n[}`, and hence that the fibres have no boundary exactly
when `i_{k+1}` covers `i_k` for `p ≤ k < n`. Only the order theory is checked here.

What is modelled. `I` is any partial order, a flag a finite chain `D : Finset I`, `m = i_p` a
term of `D` (so `d` is the terms of `D` below `m`) and `t = i_n` its last term. `gaps D m` is the
union of the open intervals between consecutive terms of `D` from `m` on, which is their ordinal
sum (`lt_of_mem_Ioo`). `Above D m t e` says that `e` is a flag containing `D` with the same terms
up to `m` and the same last term.
* `mem_gaps_iff`: the ordinal sum is the set of points off `D`, strictly between `m` and `t`, and
  comparable with every term of `D`;
* `aboveEquiv`, `aboveEquiv_eq_empty`, `aboveEquiv_subset`: `e ↦ e \ D` is an order isomorphism
  from these `e` onto the flags of the ordinal sum, `D` itself going to the empty flag;
* `gaps_eq_empty_iff`, `flags_gaps_iff`, `above_eq_iff`: the ordinal sum, equivalently its set of
  non-empty flags, equivalently the set of `e ≠ D`, is empty exactly when every step of `D` from
  `m` on is a cover; the terms below `m` do not intervene.

Not formalised: the unfolding itself, the manifolds with boundary `Σ_d`, the fibrations, the
cylindrical stratification of their boundaries and the identification of the boundary strata
with the `Σ_e`; Mathlib has no stratified spaces.
-/

namespace Grothendieck.Folder150.Flags

variable {I : Type*} [PartialOrder I] {D e : Finset I} {m t a b x : I}

/-- `a < b` are consecutive terms of the flag `D`. -/
def Consec (D : Finset I) (a b : I) : Prop := a ∈ D ∧ b ∈ D ∧ a < b ∧ ∀ c ∈ D, ¬(a < c ∧ c < b)

/-- The ordinal sum `I_{]i_p,i_{p+1}[} ⊔ … ⊔ I_{]i_{n-1},i_n[}`, `m = i_p`, inside `I`. -/
def gaps (D : Finset I) (m : I) : Set I := {x | ∃ a b, Consec D a b ∧ m ≤ a ∧ x ∈ Set.Ioo a b}

/-- The flags `e ⊇ D` with the same terms as `D` up to `m` and the same last term `t`. -/
def Above (D : Finset I) (m t : I) (e : Finset I) : Prop :=
  IsChain (· ≤ ·) (e : Set I) ∧ D ⊆ e ∧ (∀ x ∈ e, x ≤ m → x ∈ D) ∧ ∀ x ∈ e, x ≤ t

variable (hD : IsChain (· ≤ ·) (D : Set I)) (hm : m ∈ D) (ht : t ∈ D) (htop : ∀ x ∈ D, x ≤ t)
include hD

/-- The union is an ordinal sum: the interval of a lower step lies below that of a higher one. -/
theorem lt_of_mem_Ioo {a' b' y : I} (h : Consec D a b) (h' : Consec D a' b')
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a' b') (ha : a < a') : x < y := by
  refine hx.2.trans_le ((hD.total h'.1 h.2.1).elim (fun h₁ => ?_) id) |>.trans hy.1
  exact h₁.eq_or_lt.elim (·.ge) fun h₁ => (h.2.2.2 a' h'.1 ⟨ha, h₁⟩).elim

include hm ht htop in
theorem mem_gaps_iff : x ∈ gaps D m ↔ x ∉ D ∧ m < x ∧ x < t ∧ ∀ y ∈ D, x ≤ y ∨ y ≤ x := by
  classical
  constructor
  · rintro ⟨a, b, ⟨ha, hb, -, hc⟩, hma, hax, hxb⟩
    refine ⟨fun hx => hc x hx ⟨hax, hxb⟩, hma.trans_lt hax, hxb.trans_le (htop b hb), fun y hy => ?_⟩
    obtain hya | hay := hD.total hy ha
    · exact .inr (hya.trans hax.le)
    obtain hyb | hby := hD.total hy hb
    · obtain h | rfl := hay.lt_or_eq
      · obtain h' | rfl := hyb.lt_or_eq
        · exact (hc y hy ⟨h, h'⟩).elim
        · exact .inl hxb.le
      · exact .inr hax.le
    · exact .inl (hxb.le.trans hby)
  · rintro ⟨hxD, hmx, hxt, hcomp⟩
    obtain ⟨a, haL, haM⟩ := (D.filter (· < x)).exists_maximal ⟨m, by simp [hm, hmx]⟩
    obtain ⟨b, hbU, hbM⟩ := (D.filter (x < ·)).exists_minimal ⟨t, by simp [ht, hxt]⟩
    simp only [Finset.mem_filter] at haL hbU haM hbM
    refine ⟨a, b, ⟨haL.1, hbU.1, haL.2.trans hbU.2, fun c hc ⟨hac, hcb⟩ => ?_⟩, ?_, haL.2, hbU.2⟩
    · obtain hxc | hcx := hcomp c hc
      · obtain h | rfl := hxc.lt_or_eq
        · exact hcb.not_ge (hbM ⟨hc, h⟩ hcb.le)
        · exact hxD hc
      · obtain h | rfl := hcx.lt_or_eq
        · exact hac.not_ge (haM ⟨hc, h⟩ hac.le)
        · exact hxD hc
    · exact (hD.total hm haL.1).elim id fun h => haM ⟨hm, hmx⟩ h

variable [DecidableEq I]

include hm ht htop in
theorem above_iff : Above D m t e ↔ IsChain (· ≤ ·) (e : Set I) ∧ D ⊆ e ∧
    ((e \ D : Finset I) : Set I) ⊆ gaps D m := by
  refine ⟨fun ⟨he, hDe, hlo, hhi⟩ => ⟨he, hDe, fun x hx => ?_⟩, fun ⟨he, hDe, hg⟩ => ⟨he, hDe,
    fun x hx hxm => ?_, fun x hx => ?_⟩⟩
  · simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx
    refine (mem_gaps_iff hD hm ht htop).2 ⟨hx.2, ?_, (hhi x hx.1).lt_of_ne ?_,
      fun y hy => he.total hx.1 (hDe hy)⟩
    · exact ((he.total (hDe hm) hx.1).resolve_right fun h => hx.2 (hlo x hx.1 h)).lt_of_ne
        (by rintro rfl; exact hx.2 hm)
    · rintro rfl; exact hx.2 ht
  all_goals by_contra! h
  · have := ((mem_gaps_iff hD hm ht htop).1 (hg (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hx, h⟩)))).2.1
    exact this.not_ge hxm
  · exact h (if hxD : x ∈ D then htop x hxD else
      ((mem_gaps_iff hD hm ht htop).1 (hg (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hx, hxD⟩)))).2.2.1.le)

include hm ht htop in
/-- `e ↦ e \ D` identifies the flags above `D` with the flags of the ordinal sum. -/
def aboveEquiv : {e // Above D m t e} ≃ {c : Finset I // IsChain (· ≤ ·) (c : Set I) ∧
    (c : Set I) ⊆ gaps D m} where
  toFun e := ⟨e.1 \ D, ((above_iff hD hm ht htop).1 e.2).1.mono (by simp),
    ((above_iff hD hm ht htop).1 e.2).2.2⟩
  invFun c := ⟨c.1 ∪ D, (above_iff hD hm ht htop).2 ⟨by
    rw [Finset.coe_union, isChain_union]
    exact ⟨c.2.1, hD, fun x hx y hy _ =>
      (((mem_gaps_iff hD hm ht htop).1 (c.2.2 hx)).2.2.2 y hy)⟩, Finset.subset_union_right,
    by rw [Finset.union_sdiff_right]; exact (Finset.coe_subset.2 Finset.sdiff_subset).trans c.2.2⟩⟩
  left_inv e := Subtype.ext (Finset.sdiff_union_of_subset e.2.2.1)
  right_inv c := Subtype.ext (Finset.union_sdiff_cancel_right (Finset.disjoint_left.2
    fun _ hx => ((mem_gaps_iff hD hm ht htop).1 (c.2.2 hx)).1))

theorem aboveEquiv_eq_empty (e : {e // Above D m t e}) :
    (aboveEquiv hD hm ht htop e).1 = ∅ ↔ e.1 = D := by
  exact Finset.sdiff_eq_empty_iff_subset.trans ⟨(·.antisymm e.2.2.1), (·.le)⟩

theorem aboveEquiv_subset (e e' : {e // Above D m t e}) :
    (aboveEquiv hD hm ht htop e).1 ⊆ (aboveEquiv hD hm ht htop e').1 ↔ e.1 ⊆ e'.1 := by
  change e.1 \ D ⊆ e'.1 \ D ↔ _
  exact ⟨fun h x hx => if hxD : x ∈ D then e'.2.2.1 hxD else
    (Finset.mem_sdiff.1 (h (Finset.mem_sdiff.2 ⟨hx, hxD⟩))).1, (Finset.sdiff_subset_sdiff · le_rfl)⟩

omit hD [DecidableEq I] in
/-- (a): the ordinal sum is empty exactly when every step of `D` from `m` on is a cover. -/
theorem gaps_eq_empty_iff : gaps D m = ∅ ↔ ∀ a b, Consec D a b → m ≤ a → a ⋖ b := by
  simp only [Set.eq_empty_iff_forall_notMem, gaps, Set.mem_ofPred_eq, not_exists, not_and]
  exact ⟨fun h a b hab hm => ⟨hab.2.2.1, fun c h₁ h₂ => h c a b hab hm ⟨h₁, h₂⟩⟩,
    fun h x a b hab hm hx => (h a b hab hm).2 hx.1 hx.2⟩

omit hD [DecidableEq I] in
/-- (a), as stated: the ordinal sum has no non-empty flag exactly when each step is a cover. -/
theorem flags_gaps_iff : (∀ c : Finset I, IsChain (· ≤ ·) (c : Set I) →
    (c : Set I) ⊆ gaps D m → c = ∅) ↔ ∀ a b, Consec D a b → m ≤ a → a ⋖ b := by
  rw [← gaps_eq_empty_iff]
  refine ⟨fun h => Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_,
    fun h c _ hc => Finset.coe_eq_empty.1 (Set.subset_eq_empty hc h)⟩
  simpa using h {x} (by simp) (by simpa)

include hm ht htop in
/-- (b) with (a): `D` is the only flag above itself, i.e. the fibres of `Σ_{d'} → Σ_d` have no
boundary strata, exactly when every step of `D` from `m = i_p` on is a cover. -/
theorem above_eq_iff : (∀ e, Above D m t e → e = D) ↔ ∀ a b, Consec D a b → m ≤ a → a ⋖ b := by
  rw [← flags_gaps_iff]
  refine ⟨fun h c hc hcg => ?_, fun h e he => ?_⟩
  · have := (aboveEquiv_eq_empty hD hm ht htop _).2 (h _ ((aboveEquiv hD hm ht htop).symm
      ⟨c, hc, hcg⟩).2)
    rwa [Equiv.apply_symm_apply] at this
  · exact (aboveEquiv_eq_empty hD hm ht htop ⟨e, he⟩).1 (h _ (aboveEquiv hD hm ht htop ⟨e, he⟩).2.1
      (aboveEquiv hD hm ht htop ⟨e, he⟩).2.2)

end Grothendieck.Folder150.Flags
