module

public import Mathlib
public import Grothendieck.IhesSGA6_1_5
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section


/-!
# IHÉS FG_IL_5_SGA6_1_4 (with FG_IL_5_SGA6_1_3): pseudo-coherence relative to a class `C₀`

Two autograph states of the notes on finiteness conditions in derived categories, Fonds
Grothendieck–Illusie (IHÉS), FG_IL_5_SGA6_1_3 (« version I », views 1–9) and FG_IL_5_SGA6_1_4
(« version II », views 1–8). An abelian category `C` and a full subcategory `C₀` are given, with
three hypotheses: (A) `C₀` is stable under finite sums; (B) for every epimorphism `A ↠ B` with
`B ∈ C₀` some `B' → A` with `B' ∈ C₀` has an epimorphic composite `B' → B`; (C) in an exact
sequence `Lₙ → ⋯ → L₀ → 0` with the `Lᵢ` in `C₀`, the kernel of the last map is a quotient of an
object of `C₀`. A complex is `C₀`-pseudo-coherent in degrees `≥ i₀` if some bounded-above complex
of objects of `C₀` maps to it by an isomorphism on `Hⁱ` for `i > i₀` and an epimorphism on `H^{i₀}`
(Lemme 1 gives four equivalent forms). The Theorem (1_4 view 5): in an exact triangle
`L' → L → L'' → L'[1]` with `L'` pseudo-coherent in degrees `≥ i₀`, `L` is iff `L''` is. Cor. 1–2
shift the degrees; Cor. 3: an object `A` is pseudo-coherent in degrees `≥ -n` iff there is an exact
sequence `Lₙ → ⋯ → L₀ → A → 0` with the `Lᵢ` in `C₀`; Cor. 5: direct factors; Cor. 8: a larger
class `C₁ ⊇ C₀` of `C₀`-pseudo-coherent objects stable under finite sums satisfies (A), (B), (C)
and gives the same notion. A margin note (1_4 view 7) says that it suffices to assume (C ter),
kernels of epimorphisms between objects of `C₀` lie in `C₀`, instead of (C). 1_3 view 4 warns that
`D₀ᵇ ≠ Dᵇ ∩ D₀⁻` in general, for a noetherian non-regular ring and `C₀` the free modules of finite
type.

**The setting here.** `C` is the category of left modules over a ring `R` (`ModuleCat.{v} R`),
`C₀` an arbitrary predicate on it: no projectivity, which is the difference with
`IhesSGA6_1_5` (there `C₀` is the free modules of finite type). The formalisation stays at the
level of objects: an object `A` is put in degree `0`, and its pseudo-coherence in degrees `≥ -n`
is taken in the form of Cor. 3, `PC C₀ n A`, by recursion (`A` is a quotient of an object of
`C₀`; for `n + 1`, some surjection from an object of `C₀` has a kernel in `PC C₀ n`). An exact
triangle of objects is a short exact sequence `0 → A' → A → A'' → 0` (`IsSES`). Hypothesis (C) is
stated with the iterated kernels `Syz C₀ k` of exact sequences `L_k → ⋯ → L₀ → 0`.

**What is proved,** under (A), (B), (C):
* `pc_iff_of_isSES`: **the Theorem** for short exact sequences: if `A'` is in `PC n`, then `A` is
  iff `A''` is;
* `pc_succ_iff_of_isSES_middle`: **Cor. 1**: if `A ∈ PC (n+1)`, then `A'' ∈ PC (n+1)` iff
  `A' ∈ PC n`;
* `pc_iff_of_isSES_right`: **Cor. 2**: if `A'' ∈ PC (n+1)`, then `A' ∈ PC n` iff `A ∈ PC n`;
* `pc_succ_iff_ker`: for any `P ∈ C₀` and any surjection `P ↠ A`, `A ∈ PC (n+1)` iff the kernel
  is in `PC n`: the presentation in Cor. 3 may start from any epimorphism (the inductive step in
  the page's proof of Cor. 3, and Lemme 2 of 1_3);
* `pc_prod_iff`: **Cor. 5** for objects: `A × B ∈ PC n` iff `A, B ∈ PC n`;
* `cor8_pc_iff`, `cor8_condB`, `cor8_condC`: **Cor. 8** for objects: `C₁` satisfies (B) and (C)
  and `C₁`-pseudo-coherence is `C₀`-pseudo-coherence (`C₁` satisfies (A) by hypothesis);
* `condC_of_condCter`: the margin note, (C ter) implies (C);
* `pc_finFree_iff`: for `C₀` the modules `Rᵏ`, `PC C₀ n` is `IsNPresented R n` of `IhesSGA6_1_5`;
* `zmod4_pc`, `zmod4_not_finRes`: the example of 1_3 view 4, over the non-regular local ring
  `ℤ/4` with `C₀` the free modules of finite type: the ideal `2ℤ/4` is pseudo-coherent but has no
  finite resolution by free modules of finite type (its order, 2, is not a power of 4).

The proof is the edition's: one simultaneous induction on `n` for the two halves of the Theorem,
with the kernel statement (`ker_pc`) as the bridge; (B) replaces the lifting property of
projectives by covering a fibre product, and (C) enters only through the kernels of surjections
between objects of `C₀` and their iterates.

**Not formalised.** Complexes and the derived category: Lemme 1 (the four equivalent definitions)
and Lemme 1.1–1.4, the Theorem and Cor. 1–2 for triangles that do not come from short exact
sequences of objects, Cor. 4, 6, 7 (complexes and their cohomology), the equivalences
`D₀⁻ → D₁⁻ → D⁻` of Cor. 8, Cor. 9 and (C bis) (finite resolutions, `D₀ᵇ ≃ D₁ᵇ`), the
« Application aux K », the general abelian category (only modules are treated), and, in the example,
the stronger statement that `2ℤ/4` is not quasi-isomorphic to a bounded complex of free modules.
-/

namespace Grothendieck.IhesSGA6_1_4

open Function LinearMap

universe u v

section General

variable {R : Type u} [Ring R]

/-- `PC C₀ n A`: there is an exact sequence `Lₙ → ⋯ → L₀ → A → 0` with the `Lᵢ` in `C₀`, the
form of Cor. 3 of pseudo-coherence in degrees `≥ -n`, by recursion on `n`. -/
def PC (C₀ : ModuleCat.{v} R → Prop) : ℕ → ModuleCat.{v} R → Prop
  | 0, A => ∃ L : ModuleCat.{v} R, C₀ L ∧ ∃ f : L →ₗ[R] A, Surjective f
  | n + 1, A => ∃ L : ModuleCat.{v} R, C₀ L ∧ ∃ f : L →ₗ[R] A, Surjective f ∧
      PC C₀ n (ModuleCat.of R (ker f))

/-- `Syz C₀ k Z`: `Z` is the kernel of the last map of an exact sequence `L_k → ⋯ → L₀ → 0` with
the `Lᵢ` in `C₀` (`Z = L₀` for `k = 0`). -/
def Syz (C₀ : ModuleCat.{v} R → Prop) : ℕ → ModuleCat.{v} R → Prop
  | 0, Z => C₀ Z
  | k + 1, Z => ∃ L : ModuleCat.{v} R, C₀ L ∧ ∃ Z' : ModuleCat.{v} R, Syz C₀ k Z' ∧
      ∃ f : L →ₗ[R] Z', Surjective f ∧ Nonempty (Z ≃ₗ[R] ker f)

/-- Condition (A): `C₀` contains the zero module and is stable under binary sums. -/
structure CondA (C₀ : ModuleCat.{v} R → Prop) : Prop where
  zero : C₀ (ModuleCat.of R PUnit.{v + 1})
  prod : ∀ X Y : ModuleCat.{v} R, C₀ X → C₀ Y → C₀ (ModuleCat.of R (X × Y))

/-- Condition (B): every surjection onto an object of `C₀` is covered by an object of `C₀`. -/
def CondB (C₀ : ModuleCat.{v} R → Prop) : Prop :=
  ∀ (A B : ModuleCat.{v} R), C₀ B → ∀ u : A →ₗ[R] B, Surjective u →
    ∃ B' : ModuleCat.{v} R, C₀ B' ∧ ∃ w : B' →ₗ[R] A, Surjective (u ∘ₗ w)

/-- Condition (C): the kernels `Syz C₀ k` are quotients of objects of `C₀`. -/
def CondC (C₀ : ModuleCat.{v} R → Prop) : Prop := ∀ k Z, Syz C₀ k Z → PC C₀ 0 Z

/-- Condition (C ter): the kernel of a surjection between objects of `C₀` is isomorphic to an
object of `C₀`. -/
def CondCter (C₀ : ModuleCat.{v} R → Prop) : Prop :=
  ∀ L L' : ModuleCat.{v} R, C₀ L → C₀ L' → ∀ f : L →ₗ[R] L', Surjective f →
    ∃ L'' : ModuleCat.{v} R, C₀ L'' ∧ Nonempty (ker f ≃ₗ[R] L'')

/-- A short exact sequence `0 → A' → A → A'' → 0`. -/
structure IsSES {A' A A'' : ModuleCat.{v} R} (i : A' →ₗ[R] A) (p : A →ₗ[R] A'') : Prop where
  inj : Injective i
  surj : Surjective p
  exact : Exact i p

variable {C₀ C₁ : ModuleCat.{v} R → Prop}

theorem PC.of_equiv : ∀ {n : ℕ} {A B : ModuleCat.{v} R}, PC C₀ n A → (A ≃ₗ[R] B) → PC C₀ n B
  | 0, _, _, ⟨L, hL, f, hf⟩, e => ⟨L, hL, e.toLinearMap ∘ₗ f, e.surjective.comp hf⟩
  | _ + 1, _, _, ⟨L, hL, f, hf, hK⟩, e => ⟨L, hL, e.toLinearMap ∘ₗ f, e.surjective.comp hf,
      PC.of_equiv hK (LinearEquiv.ofEq _ _ (LinearEquiv.ker_comp e f).symm)⟩

theorem PC.of_succ : ∀ {n : ℕ} {A : ModuleCat.{v} R}, PC C₀ (n + 1) A → PC C₀ n A
  | 0, _, ⟨L, hL, f, hf, _⟩ => ⟨L, hL, f, hf⟩
  | _ + 1, _, ⟨L, hL, f, hf, hK⟩ => ⟨L, hL, f, hf, PC.of_succ hK⟩

theorem PC.of_le {m n : ℕ} {A : ModuleCat.{v} R} (hmn : m ≤ n) (h : PC C₀ n A) : PC C₀ m A := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

theorem PC.zero_of_surjective {A B : ModuleCat.{v} R} (h : PC C₀ 0 A) (p : A →ₗ[R] B)
    (hp : Surjective p) : PC C₀ 0 B := by
  obtain ⟨L, hL, f, hf⟩ := h
  exact ⟨L, hL, p ∘ₗ f, hp.comp hf⟩

/-- Pseudo-coherence for `C₀` implies it for any larger class. -/
theorem PC.mono (h01 : ∀ X, C₀ X → C₁ X) :
    ∀ {n : ℕ} {A : ModuleCat.{v} R}, PC C₀ n A → PC C₁ n A
  | 0, _, ⟨L, hL, f, hf⟩ => ⟨L, h01 L hL, f, hf⟩
  | _ + 1, _, ⟨L, hL, f, hf, hK⟩ => ⟨L, h01 L hL, f, hf, PC.mono h01 hK⟩

theorem PC.of_subsingleton (hz : C₀ (ModuleCat.of R PUnit.{v + 1})) :
    ∀ (n : ℕ) (A : ModuleCat.{v} R), Subsingleton A → PC C₀ n A
  | 0, _, _ => ⟨_, hz, 0, fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩
  | n + 1, _, _ => ⟨_, hz, 0, fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩,
      PC.of_subsingleton hz n _ (by dsimp; infer_instance)⟩

/-- An object of `C₀` is pseudo-coherent. -/
theorem PC.of_mem (hz : C₀ (ModuleCat.of R PUnit.{v + 1})) {L : ModuleCat.{v} R} (hL : C₀ L) :
    ∀ n, PC C₀ n L
  | 0 => ⟨L, hL, LinearMap.id, surjective_id⟩
  | n + 1 => ⟨L, hL, LinearMap.id, surjective_id, PC.of_subsingleton hz n _
      ⟨fun a b => Subtype.ext ((mem_ker.1 a.2).trans (mem_ker.1 b.2).symm)⟩⟩

/-- The kernel of a short exact sequence is its first term. -/
noncomputable def IsSES.kerEquiv {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A}
    {p : A →ₗ[R] A''} (h : IsSES i p) : A' ≃ₗ[R] ModuleCat.of R (ker p) :=
  (LinearEquiv.ofInjective i h.inj).trans (LinearEquiv.ofEq _ _ h.exact.linearMap_ker_eq.symm)

theorem IsSES.pc_iff {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A} {p : A →ₗ[R] A''}
    (h : IsSES i p) {n : ℕ} : PC C₀ n A' ↔ PC C₀ n (ModuleCat.of R (ker p)) :=
  ⟨fun hA => hA.of_equiv h.kerEquiv, fun hK => hK.of_equiv h.kerEquiv.symm⟩

theorem isSES_ker {A A'' : ModuleCat.{v} R} (p : A →ₗ[R] A'') (hp : Surjective p) :
    IsSES (A' := ModuleCat.of R (ker p)) (ker p).subtype p :=
  ⟨Subtype.val_injective, hp, exact_subtype_ker_map p⟩

/-- For `f : M ↠ N` and `q : N → P`, the sequence `0 → ker f → ker (q ∘ f) → ker q → 0`. -/
theorem isSES_ker_comp {M N P : ModuleCat.{v} R} (f : M →ₗ[R] N) (q : N →ₗ[R] P)
    (hf : Surjective f) :
    IsSES (A' := ModuleCat.of R (ker f)) (A := ModuleCat.of R (ker (q ∘ₗ f)))
      (A'' := ModuleCat.of R (ker q))
      (Submodule.inclusion (fun x hx => by simp [mem_ker.1 hx]))
      (LinearMap.codRestrict (ker q) (f ∘ₗ (ker (q ∘ₗ f)).subtype)
        (fun x => mem_ker.2 (mem_ker.1 x.2))) := by
  refine ⟨Submodule.inclusion_injective _, ?_, ?_⟩
  · intro y
    obtain ⟨m, hm⟩ := hf y.1
    exact ⟨⟨m, mem_ker.2 (by simp [hm, mem_ker.1 y.2])⟩, Subtype.ext hm⟩
  · intro z
    constructor
    · intro hz
      exact ⟨⟨z.1, mem_ker.2 (congrArg Subtype.val hz)⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact Subtype.ext (mem_ker.1 w.2)

/-- The kernels of a surjection between objects of `C₀`, and their iterates, are pseudo-coherent
under (C). -/
theorem Syz.pc (hC : CondC C₀) : ∀ (n k : ℕ) (Z : ModuleCat.{v} R), Syz C₀ k Z → PC C₀ n Z
  | 0, k, Z, h => hC k Z h
  | n + 1, k, Z, h => by
    obtain ⟨L, hL, f, hf⟩ := hC k Z h
    exact ⟨L, hL, f, hf, Syz.pc hC n (k + 1) _ ⟨L, hL, Z, h, f, hf, ⟨LinearEquiv.refl _ _⟩⟩⟩

theorem pc_ker_of_mem (hC : CondC C₀) {L L' : ModuleCat.{v} R} (hL : C₀ L) (hL' : C₀ L')
    (f : L →ₗ[R] L') (hf : Surjective f) (n : ℕ) : PC C₀ n (ModuleCat.of R (ker f)) :=
  Syz.pc hC n 1 _ ⟨L, hL, L', hL', f, hf, ⟨LinearEquiv.refl _ _⟩⟩

/-! ### The fibre product -/

section Pullback

variable {M N P : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The fibre product of `f : M → P` and `g : N → P`, as a submodule of `M × N`. -/
abbrev pb (f : M →ₗ[R] P) (g : N →ₗ[R] P) : Submodule R (M × N) :=
  ker (f ∘ₗ LinearMap.fst R M N - g ∘ₗ LinearMap.snd R M N)

theorem pb_spec {f : M →ₗ[R] P} {g : N →ₗ[R] P} (e : pb f g) : f e.1.1 = g e.1.2 := by
  have := mem_ker.1 e.2
  rw [LinearMap.sub_apply, sub_eq_zero] at this
  exact this

theorem pb_fst_surj {f : M →ₗ[R] P} {g : N →ₗ[R] P} (hg : Surjective g) :
    Surjective (LinearMap.fst R M N ∘ₗ (pb f g).subtype) := by
  intro m
  obtain ⟨n, hn⟩ := hg (f m)
  exact ⟨⟨(m, n), by simp [hn]⟩, rfl⟩

theorem pb_snd_surj {f : M →ₗ[R] P} {g : N →ₗ[R] P} (hf : Surjective f) :
    Surjective (LinearMap.snd R M N ∘ₗ (pb f g).subtype) := by
  intro n
  obtain ⟨m, hm⟩ := hf (g n)
  exact ⟨⟨(m, n), by simp [hm]⟩, rfl⟩

end Pullback

/-! ### The induction -/

/-- The quotient half of the Theorem at level `n`. -/
def T1 (C₀ : ModuleCat.{v} R → Prop) (n : ℕ) : Prop :=
  ∀ (A' A A'' : ModuleCat.{v} R) (i : A' →ₗ[R] A) (p : A →ₗ[R] A''), IsSES i p →
    PC C₀ n A' → PC C₀ n A → PC C₀ n A''

/-- The extension half of the Theorem at level `n`. -/
def T2 (C₀ : ModuleCat.{v} R → Prop) (n : ℕ) : Prop :=
  ∀ (A' A A'' : ModuleCat.{v} R) (i : A' →ₗ[R] A) (p : A →ₗ[R] A''), IsSES i p →
    PC C₀ n A' → PC C₀ n A'' → PC C₀ n A

theorem t1_zero : T1 C₀ 0 := fun _ _ _ _ p h _ hA => hA.zero_of_surjective p h.surj

/-- The horseshoe step under (B): from covers `g' : L' ↠ A'` and `g'' : L'' ↠ A''`, a
cover `Φ : L' × P ↠ A` with `P ∈ C₀`, and the exact sequence `0 → ker g' → ker Φ → ker h → 0`
with `h : P ↠ A''`. -/
theorem horseshoe (hB : CondB C₀) {A' A A'' : ModuleCat.{v} R}
    {i : A' →ₗ[R] A} {p : A →ₗ[R] A''} (h : IsSES i p) {L' L'' : ModuleCat.{v} R}
    (hL'' : C₀ L'') (g' : L' →ₗ[R] A') (hg' : Surjective g')
    (g'' : L'' →ₗ[R] A'') (hg'' : Surjective g'') :
    ∃ P : ModuleCat.{v} R, C₀ P ∧ ∃ (Φ : ModuleCat.of R (L' × P) →ₗ[R] A)
      (q : P →ₗ[R] A''), Surjective Φ ∧ Surjective q ∧
      ∃ (j : ModuleCat.of R (ker g') →ₗ[R] ModuleCat.of R (ker Φ))
        (r : ModuleCat.of R (ker Φ) →ₗ[R] ModuleCat.of R (ker q)), IsSES j r := by
  let E := ModuleCat.of R (pb p g'')
  let s : E →ₗ[R] L'' := LinearMap.snd R A L'' ∘ₗ (pb p g'').subtype
  obtain ⟨P, hP, w, hw⟩ := hB E L'' hL'' s (pb_snd_surj h.surj)
  let t : P →ₗ[R] A := LinearMap.fst R A L'' ∘ₗ (pb p g'').subtype ∘ₗ w
  have ht : ∀ y, p (t y) = g'' (s (w y)) := fun y => pb_spec (w y)
  let Φ : ModuleCat.of R (L' × P) →ₗ[R] A := LinearMap.coprod (i ∘ₗ g') t
  have hΦ : ∀ x y, Φ (x, y) = i (g' x) + t y := fun _ _ => rfl
  have hpi : ∀ a', p (i a') = 0 := fun a' => h.exact.apply_apply_eq_zero a'
  refine ⟨P, hP, Φ, g'' ∘ₗ s ∘ₗ w, ?_, hg''.comp hw, ?_⟩
  · intro a
    obtain ⟨l, hl⟩ := hg'' (p a)
    obtain ⟨y, hy⟩ := hw l
    have hy' : s (w y) = l := hy
    have h0 : p (a - t y) = 0 := by rw [map_sub, ht, hy', hl, sub_self]
    obtain ⟨a', ha'⟩ := (h.exact _).1 h0
    obtain ⟨x, hx⟩ := hg' a'
    exact ⟨(x, y), by rw [hΦ, hx, ha', sub_add_cancel]⟩
  · let j : ModuleCat.of R (ker g') →ₗ[R] ModuleCat.of R (ker Φ) :=
      LinearMap.codRestrict (ker Φ) (LinearMap.inl R L' P ∘ₗ (ker g').subtype)
        (fun x => mem_ker.2 (by simp [hΦ, mem_ker.1 x.2]))
    have hr : ∀ z : ker Φ, (g'' ∘ₗ s ∘ₗ w) z.1.2 = 0 := by
      intro z
      have hz : i (g' z.1.1) + t z.1.2 = 0 := mem_ker.1 z.2
      have : p (t z.1.2) = 0 := by
        rw [eq_neg_of_add_eq_zero_right hz, map_neg, hpi, neg_zero]
      rw [← this, ht]; rfl
    let r : ModuleCat.of R (ker Φ) →ₗ[R] ModuleCat.of R (ker (g'' ∘ₗ s ∘ₗ w)) :=
      LinearMap.codRestrict (ker (g'' ∘ₗ s ∘ₗ w)) (LinearMap.snd R L' P ∘ₗ (ker Φ).subtype)
        (fun z => mem_ker.2 (hr z))
    refine ⟨j, r, ⟨?_, ?_, ?_⟩⟩
    · intro x x' hxx
      exact Subtype.ext (congrArg (fun z : ker Φ => z.1.1) hxx)
    · intro y
      have hy : p (t y.1) = 0 := by rw [ht]; exact mem_ker.1 y.2
      obtain ⟨a', ha'⟩ := (h.exact _).1 hy
      obtain ⟨x, hx⟩ := hg' a'
      refine ⟨⟨(-x, y.1), mem_ker.2 ?_⟩, rfl⟩
      rw [hΦ, map_neg, map_neg, hx, ha', neg_add_cancel]
    · intro z
      constructor
      · intro hz
        have hz2 : z.1.2 = 0 := congrArg Subtype.val hz
        have h1 : i (g' z.1.1) + t z.1.2 = 0 := mem_ker.1 z.2
        rw [hz2, map_zero, add_zero] at h1
        have h2 : g' z.1.1 = 0 := h.inj (by rw [h1, map_zero])
        refine ⟨⟨z.1.1, mem_ker.2 h2⟩, Subtype.ext ?_⟩
        show (z.1.1, (0 : P)) = z.1
        rw [← hz2]
      · rintro ⟨x, rfl⟩
        rfl

theorem t2_zero (hA : CondA C₀) (hB : CondB C₀) : T2 C₀ 0 := by
  intro A' A A'' i p h ⟨L', hL', g', hg'⟩ ⟨L'', hL'', g'', hg''⟩
  obtain ⟨P, hP, Φ, -, hΦ, -⟩ := horseshoe hB h hL'' g' hg' g'' hg''
  exact ⟨_, hA.prod L' P hL' hP, Φ, hΦ⟩

/-- Cor. 1, « ⇐ », at level `n`, from the extension half at level `n`. -/
theorem t4 {n : ℕ} (h2 : T2 C₀ n) {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A}
    {p : A →ₗ[R] A''} (h : IsSES i p) (hA' : PC C₀ n A') (hA : PC C₀ (n + 1) A) :
    PC C₀ (n + 1) A'' := by
  obtain ⟨L, hL, f, hf, hK⟩ := hA
  exact ⟨L, hL, p ∘ₗ f, h.surj.comp hf, h2 _ _ _ _ _ (isSES_ker_comp f p hf) hK (h.pc_iff.1 hA')⟩

theorem t1_succ {n : ℕ} (h2 : T2 C₀ n) : T1 C₀ (n + 1) :=
  fun _ _ _ _ _ h hA' hA => t4 h2 h hA'.of_succ hA

/-- The kernel statement at level `n`: for `P ∈ C₀` and `g : P ↠ A''` with `A'' ∈ PC (n+1)`,
`ker g ∈ PC n`. -/
theorem ker_pc (hA : CondA C₀) (hB : CondB C₀) (hC : CondC C₀) {n : ℕ} (h1 : T1 C₀ n)
    (h2 : T2 C₀ n) {P A'' : ModuleCat.{v} R} (hP : C₀ P) (g : P →ₗ[R] A'') (hg : Surjective g)
    (hA'' : PC C₀ (n + 1) A'') : PC C₀ n (ModuleCat.of R (ker g)) := by
  obtain ⟨L, hL, f, hf, hM⟩ := hA''
  let E := ModuleCat.of R (pb f g)
  let s₁ : E →ₗ[R] L := LinearMap.fst R L P ∘ₗ (pb f g).subtype
  let s₂ : E →ₗ[R] P := LinearMap.snd R L P ∘ₗ (pb f g).subtype
  obtain ⟨Q₂, hQ₂, v₂, hv₂⟩ := hB E L hL s₁ (pb_fst_surj hg)
  obtain ⟨Q₁, hQ₁, v₁, hv₁⟩ := hB E P hP s₂ (pb_snd_surj hf)
  let Q := ModuleCat.of R (Q₁ × Q₂)
  let w : Q →ₗ[R] E := LinearMap.coprod v₁ v₂
  let α : Q →ₗ[R] L := s₁ ∘ₗ w
  let γ : Q →ₗ[R] P := s₂ ∘ₗ w
  have hα : Surjective α := by
    intro l
    obtain ⟨q, hq⟩ := hv₂ l
    exact ⟨(0, q), show s₁ (v₁ 0 + v₂ q) = l by rw [map_zero, zero_add]; exact hq⟩
  have hγ : Surjective γ := by
    intro y
    obtain ⟨q, hq⟩ := hv₁ y
    exact ⟨(q, 0), show s₂ (v₁ q + v₂ 0) = y by rw [map_zero, add_zero]; exact hq⟩
  have hk : f ∘ₗ α = g ∘ₗ γ := LinearMap.ext fun q => pb_spec (w q)
  have hQ : C₀ Q := hA.prod Q₁ Q₂ hQ₁ hQ₂
  have hkα : PC C₀ n (ModuleCat.of R (ker (f ∘ₗ α))) :=
    h2 _ _ _ _ _ (isSES_ker_comp α f hα) (pc_ker_of_mem hC hQ hL α hα n) hM
  rw [hk] at hkα
  exact h1 _ _ _ _ _ (isSES_ker_comp γ g hγ) (pc_ker_of_mem hC hQ hP γ hγ n) hkα

theorem t2_succ (hA : CondA C₀) (hB : CondB C₀) {n : ℕ} (h2 : T2 C₀ n)
    (hK : ∀ {P A'' : ModuleCat.{v} R}, C₀ P → ∀ g : P →ₗ[R] A'', Surjective g →
      PC C₀ (n + 1) A'' → PC C₀ n (ModuleCat.of R (ker g))) : T2 C₀ (n + 1) := by
  intro A' A A'' i p h ⟨L', hL', g', hg', hK'⟩ hA''
  obtain ⟨L'', hL'', g'', hg'', -⟩ := id hA''
  obtain ⟨P, hP, Φ, q, hΦ, hq, j, r, hjr⟩ := horseshoe hB h hL'' g' hg' g'' hg''
  exact ⟨_, hA.prod L' P hL' hP, Φ, hΦ, h2 _ _ _ j r hjr hK' (hK hP q hq ‹_›)⟩

theorem t12 (hA : CondA C₀) (hB : CondB C₀) (hC : CondC C₀) : ∀ n, T1 C₀ n ∧ T2 C₀ n
  | 0 => ⟨t1_zero, t2_zero hA hB⟩
  | n + 1 =>
    have ih := t12 hA hB hC n
    ⟨t1_succ ih.2, t2_succ hA hB ih.2 (fun hP g hg hA'' => ker_pc hA hB hC ih.1 ih.2 hP g hg hA'')⟩

variable (hA : CondA C₀) (hB : CondB C₀) (hC : CondC C₀)
include hA hB hC

/-- For `P ∈ C₀` and `g : P ↠ A`: `A ∈ PC (n+1)` iff `ker g ∈ PC n`, whatever the surjection. -/
theorem pc_succ_iff_ker {n : ℕ} {P A : ModuleCat.{v} R} (hP : C₀ P) (g : P →ₗ[R] A)
    (hg : Surjective g) : PC C₀ (n + 1) A ↔ PC C₀ n (ModuleCat.of R (ker g)) :=
  ⟨fun hA' => ker_pc hA hB hC (t12 hA hB hC n).1 (t12 hA hB hC n).2 hP g hg hA',
    fun hK => ⟨P, hP, g, hg, hK⟩⟩

/-- **Cor. 2**, « ⇐ »: `A ∈ PC n` and `A'' ∈ PC (n+1)` give `A' ∈ PC n`. -/
theorem pc_left_of_isSES {n : ℕ} {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A}
    {p : A →ₗ[R] A''} (h : IsSES i p) (hA' : PC C₀ n A) (hA'' : PC C₀ (n + 1) A'') :
    PC C₀ n A' := by
  rw [h.pc_iff]
  cases n with
  | zero =>
    obtain ⟨L, hL, f, hf⟩ := hA'
    have hk := (pc_succ_iff_ker hA hB hC hL (p ∘ₗ f) (h.surj.comp hf)).1 hA''
    exact hk.zero_of_surjective _ (isSES_ker_comp f p hf).surj
  | succ m =>
    obtain ⟨L, hL, f, hf, hK⟩ := hA'
    have hk := (pc_succ_iff_ker hA hB hC hL (p ∘ₗ f) (h.surj.comp hf)).1 hA''
    exact t4 (t12 hA hB hC m).2 (isSES_ker_comp f p hf) hK hk

/-- **The Theorem** (1_4 view 5), for the triangle of a short exact sequence `0 → A' → A → A'' → 0`:
if `A'` is in `PC n`, then `A` is iff `A''` is. -/
theorem pc_iff_of_isSES {n : ℕ} {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A}
    {p : A →ₗ[R] A''} (h : IsSES i p) (hA' : PC C₀ n A') : PC C₀ n A ↔ PC C₀ n A'' :=
  ⟨(t12 hA hB hC n).1 _ _ _ i p h hA', (t12 hA hB hC n).2 _ _ _ i p h hA'⟩

/-- **Cor. 1**: if `A ∈ PC (n+1)`, then `A'' ∈ PC (n+1)` iff `A' ∈ PC n`. -/
theorem pc_succ_iff_of_isSES_middle {n : ℕ} {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A}
    {p : A →ₗ[R] A''} (h : IsSES i p) (hAm : PC C₀ (n + 1) A) :
    PC C₀ (n + 1) A'' ↔ PC C₀ n A' :=
  ⟨fun hA'' => pc_left_of_isSES hA hB hC h hAm.of_succ hA'',
    fun hA' => t4 (t12 hA hB hC n).2 h hA' hAm⟩

/-- **Cor. 2**: if `A'' ∈ PC (n+1)`, then `A' ∈ PC n` iff `A ∈ PC n`. -/
theorem pc_iff_of_isSES_right {n : ℕ} {A' A A'' : ModuleCat.{v} R} {i : A' →ₗ[R] A}
    {p : A →ₗ[R] A''} (h : IsSES i p) (hA'' : PC C₀ (n + 1) A'') : PC C₀ n A' ↔ PC C₀ n A :=
  ⟨fun hA' => (t12 hA hB hC n).2 _ _ _ i p h hA' hA''.of_succ,
    fun hA' => pc_left_of_isSES hA hB hC h hA' hA''⟩

/-- **Cor. 5** for objects: a direct factor of a pseudo-coherent object is pseudo-coherent. -/
theorem pc_prod_iff {n : ℕ} {A B : ModuleCat.{v} R} :
    PC C₀ n (ModuleCat.of R (A × B)) ↔ PC C₀ n A ∧ PC C₀ n B := by
  constructor
  · intro hAB
    induction n generalizing A B with
    | zero =>
      exact ⟨hAB.zero_of_surjective (LinearMap.fst R A B) LinearMap.fst_surjective,
        hAB.zero_of_surjective (LinearMap.snd R A B) LinearMap.snd_surjective⟩
    | succ n ih =>
      obtain ⟨hA', hB'⟩ := ih hAB.of_succ
      have h₁ : IsSES (A' := B) (A := ModuleCat.of R (A × B)) (LinearMap.inr R A B)
          (LinearMap.fst R A B) :=
        ⟨LinearMap.inr_injective, LinearMap.fst_surjective, Exact.inr_fst⟩
      have h₂ : IsSES (A' := A) (A := ModuleCat.of R (A × B)) (LinearMap.inl R A B)
          (LinearMap.snd R A B) :=
        ⟨LinearMap.inl_injective, LinearMap.snd_surjective, Exact.inl_snd⟩
      exact ⟨(pc_succ_iff_of_isSES_middle hA hB hC h₁ hAB).2 hB',
        (pc_succ_iff_of_isSES_middle hA hB hC h₂ hAB).2 hA'⟩
  · rintro ⟨hA', hB'⟩
    have h₂ : IsSES (A' := A) (A := ModuleCat.of R (A × B)) (LinearMap.inl R A B)
        (LinearMap.snd R A B) :=
      ⟨LinearMap.inl_injective, LinearMap.snd_surjective, Exact.inl_snd⟩
    exact (pc_iff_of_isSES hA hB hC h₂ hA').2 hB'

omit hA hB hC

section Cor8

variable (h01 : ∀ X, C₀ X → C₁ X) (hpc : ∀ X, C₁ X → ∀ n, PC C₀ n X)
include hA hB hC h01 hpc

/-- **Cor. 8**: pseudo-coherence relative to `C₁` and to `C₀` agree. -/
theorem cor8_pc_iff : ∀ {n : ℕ} {A : ModuleCat.{v} R}, PC C₁ n A ↔ PC C₀ n A := by
  intro n
  induction n with
  | zero =>
    intro A
    exact ⟨fun ⟨L, hL, f, hf⟩ => (hpc L hL 0).zero_of_surjective f hf, PC.mono h01⟩
  | succ n ih =>
    intro A
    refine ⟨fun ⟨L, hL, f, hf, hK⟩ => ?_, PC.mono h01⟩
    exact (pc_succ_iff_of_isSES_middle hA hB hC (isSES_ker f hf) (hpc L hL (n + 1))).2
      (ih.1 hK)

omit hA hC in
/-- **Cor. 8**: `C₁` satisfies (B). -/
theorem cor8_condB : CondB C₁ := by
  intro A B hBC u hu
  obtain ⟨L₀, hL₀, g, hg⟩ := hpc B hBC 0
  let E := ModuleCat.of R (pb u g)
  obtain ⟨B', hB', w, hw⟩ := hB E L₀ hL₀ (LinearMap.snd R A L₀ ∘ₗ (pb u g).subtype)
    (pb_snd_surj hu)
  refine ⟨B', h01 _ hB', LinearMap.fst R A L₀ ∘ₗ (pb u g).subtype ∘ₗ w, ?_⟩
  have : u ∘ₗ (LinearMap.fst R A L₀ ∘ₗ (pb u g).subtype ∘ₗ w) =
      g ∘ₗ (LinearMap.snd R A L₀ ∘ₗ (pb u g).subtype ∘ₗ w) :=
    LinearMap.ext fun y => pb_spec (w y)
  rw [this]
  exact hg.comp hw

/-- **Cor. 8**: `C₁` satisfies (C). -/
theorem cor8_condC : CondC C₁ := by
  have key : ∀ k Z, Syz C₁ k Z → ∀ n, PC C₀ n Z := by
    intro k
    induction k with
    | zero => exact fun Z hZ => hpc Z hZ
    | succ k ih =>
      rintro Z ⟨L, hL, Z', hZ', f, hf, ⟨e⟩⟩ n
      have := pc_left_of_isSES hA hB hC (isSES_ker f hf) (hpc L hL n) (ih Z' hZ' (n + 1))
      exact this.of_equiv e.symm
  exact fun k Z hZ => PC.mono h01 (key k Z hZ 0)

end Cor8

/-- The margin note of 1_4 view 7: (C ter) implies (C). -/
theorem condC_of_condCter (hCt : CondCter C₀) : CondC C₀ := by
  have key : ∀ k Z, Syz C₀ k Z → ∃ M : ModuleCat.{v} R, C₀ M ∧ Nonempty (Z ≃ₗ[R] M) := by
    intro k
    induction k with
    | zero => exact fun Z hZ => ⟨Z, hZ, ⟨LinearEquiv.refl _ _⟩⟩
    | succ k ih =>
      rintro Z ⟨L, hL, Z', hZ', f, hf, ⟨e⟩⟩
      obtain ⟨M, hM, ⟨e'⟩⟩ := ih Z' hZ'
      obtain ⟨L'', hL'', ⟨e''⟩⟩ := hCt L M hL hM (e'.toLinearMap ∘ₗ f) (e'.surjective.comp hf)
      exact ⟨L'', hL'', ⟨e.trans ((LinearEquiv.ofEq _ _ (LinearEquiv.ker_comp e' f).symm).trans
        e'')⟩⟩
  intro k Z hZ
  obtain ⟨M, hM, ⟨e⟩⟩ := key k Z hZ
  exact ⟨M, hM, e.symm.toLinearMap, e.symm.surjective⟩

end General

/-! ### Free modules of finite type -/

section Free

open Grothendieck.IhesSGA6_1_5

variable {R : Type u} [Ring R]

/-- The free modules of finite type, up to isomorphism. -/
def FinFree (R : Type u) [Ring R] (X : ModuleCat.{u} R) : Prop :=
  ∃ k : ℕ, Nonempty (X ≃ₗ[R] (Fin k → R))

/-- For `C₀` the free modules of finite type, `PC` is the `n`-presentation of `IhesSGA6_1_5`. -/
theorem pc_finFree_iff : ∀ {n : ℕ} {A : ModuleCat.{u} R}, PC (FinFree R) n A ↔ IsNPresented R n A
  | 0, A => by
    constructor
    · rintro ⟨L, ⟨k, ⟨e⟩⟩, f, hf⟩
      have : Module.Finite R L := Module.Finite.equiv e.symm
      exact Module.Finite.of_surjective f hf
    · intro h
      have : Module.Finite R A := h
      obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R A
      exact ⟨ModuleCat.of R (Fin k → R), ⟨k, ⟨LinearEquiv.refl _ _⟩⟩, f, hf⟩
  | n + 1, A => by
    constructor
    · rintro ⟨L, ⟨k, ⟨e⟩⟩, f, hf, hK⟩
      refine ⟨k, f ∘ₗ e.symm.toLinearMap, hf.comp e.symm.surjective, ?_⟩
      refine (pc_finFree_iff.1 hK).of_equiv ((e.submoduleMap (ker f)).trans
        (LinearEquiv.ofEq _ _ ?_))
      rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]
    · rintro ⟨k, f, hf, hK⟩
      exact ⟨ModuleCat.of R (Fin k → R), ⟨k, ⟨LinearEquiv.refl _ _⟩⟩, f, hf,
        pc_finFree_iff.2 hK⟩

end Free

/-! ### The example of 1_3 view 4: `ℤ/4` -/

section Example

/-- Multiplication by `2` on `ℤ/4`. -/
def two : ZMod 4 →ₗ[ZMod 4] ZMod 4 := (2 : ZMod 4) • LinearMap.id

theorem ker_two_eq_range : ker two = range two := by
  ext x
  simp only [mem_ker, mem_range, two, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
  revert x
  decide

/-- The ideal `2ℤ/4`, as a `ℤ/4`-module. -/
abbrev M2 : ModuleCat.{0} (ZMod 4) := ModuleCat.of (ZMod 4) (range two)

theorem finFree_zmod4 : FinFree (ZMod 4) (ModuleCat.of (ZMod 4) (ZMod 4)) :=
  ⟨1, ⟨(LinearEquiv.funUnique (Fin 1) (ZMod 4) (ZMod 4)).symm⟩⟩

/-- The kernel of `ℤ/4 ↠ 2ℤ/4` is again `2ℤ/4`. -/
noncomputable def kerEquiv : ModuleCat.of (ZMod 4) (ker two.rangeRestrict) ≃ₗ[ZMod 4] M2 :=
  LinearEquiv.ofEq _ _ (by rw [LinearMap.ker_rangeRestrict, ker_two_eq_range])

/-- `2ℤ/4` is pseudo-coherent: `⋯ → ℤ/4 → ℤ/4 → 2ℤ/4 → 0`, multiplication by 2 each time. -/
theorem zmod4_pc : ∀ n, PC (FinFree (ZMod 4)) n M2
  | 0 => ⟨_, finFree_zmod4, two.rangeRestrict, LinearMap.surjective_rangeRestrict two⟩
  | n + 1 => ⟨_, finFree_zmod4, two.rangeRestrict, LinearMap.surjective_rangeRestrict two,
      (zmod4_pc n).of_equiv kerEquiv.symm⟩

/-- `FinRes C₀ n A`: an exact sequence `0 → Lₙ → ⋯ → L₀ → A → 0` with the `Lᵢ` in `C₀`. -/
def FinRes {R : Type u} [Ring R] (C₀ : ModuleCat.{v} R → Prop) : ℕ → ModuleCat.{v} R → Prop
  | 0, A => C₀ A
  | n + 1, A => ∃ L : ModuleCat.{v} R, C₀ L ∧ ∃ f : L →ₗ[R] A, Surjective f ∧
      FinRes C₀ n (ModuleCat.of R (ker f))

theorem card_of_finRes : ∀ (n : ℕ) (A : ModuleCat.{0} (ZMod 4)), FinRes (FinFree (ZMod 4)) n A →
    Finite A ∧ ∃ k : ℕ, Nat.card A = 4 ^ k
  | 0, A, ⟨k, ⟨e⟩⟩ => by
    refine ⟨Finite.of_equiv _ e.toEquiv.symm, k, ?_⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  | n + 1, A, ⟨L, hL, f, hf, hK⟩ => by
    obtain ⟨hLfin, a, ha⟩ := card_of_finRes 0 L hL
    obtain ⟨-, b, hb⟩ := card_of_finRes n _ hK
    have hfin : Finite A := Finite.of_surjective f hf
    refine ⟨hfin, ?_⟩
    have hcard : Nat.card L = Nat.card (ker f) * Nat.card A := by
      have h0 := Submodule.card_eq_card_quotient_mul_card (ker f)
      rw [Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv] at h0
      exact h0
    have hb' : Nat.card (ker f) = 4 ^ b := hb
    rw [ha, hb'] at hcard
    have hle : b ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 ⟨_, hcard⟩
    refine ⟨a - b, Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 4 ^ b) ?_⟩
    rw [← hcard, ← pow_add, Nat.add_sub_cancel' hle]

theorem card_M2 : Nat.card M2 = 2 := by
  have h := Submodule.card_eq_card_quotient_mul_card (ker two.rangeRestrict)
  rw [Nat.card_congr (two.rangeRestrict.quotKerEquivOfSurjective
    (LinearMap.surjective_rangeRestrict two)).toEquiv, Nat.card_congr kerEquiv.toEquiv,
    Nat.card_zmod] at h
  have h' : Nat.card M2 * Nat.card M2 = 2 * 2 := by rw [← h]
  exact Nat.mul_self_inj.1 h'

/-- The example of 1_3 view 4: over `ℤ/4`, which is noetherian and not regular, `2ℤ/4` has no
finite resolution by free modules of finite type, although it is pseudo-coherent (`zmod4_pc`). -/
theorem zmod4_not_finRes (n : ℕ) : ¬ FinRes (FinFree (ZMod 4)) n M2 := by
  intro h
  obtain ⟨-, k, hk⟩ := card_of_finRes n M2 h
  rw [card_M2] at hk
  rcases k with _ | k
  · simp at hk
  · have : 4 ≤ 4 ^ (k + 1) := Nat.le_self_pow (by omega) 4
    omega

end Example

end Grothendieck.IhesSGA6_1_4
