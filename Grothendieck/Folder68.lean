module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

@[expose] public section



/-!
# Folder 68: theories of orientation characterised by their Stokes maps (pages 49, 51)

The finding `68-orientation-stokes-axioms` (`src/content/findings.ts`) states the theorem of
page 49 of the reading (`transcripts/68/68.modern.tex`, section VI): on the groupoid of
finite-dimensional real vector spaces, a *theory of orientation* is a functor `Ω` to
two-element sets with `Ω(0) ≃ {±1}` and, for every hyperplane `W ⊂ V` and closed half-space
`V′` bounded by `W`, a Stokes bijection `St_{V′} : Ω(V) → Ω(W)`, natural in `(V, V′)`, with
`St_{V″} = τ ∘ St_{V′}` for the opposite half-space `V″`; every morphism of theories is an
isomorphism, two theories are related by exactly one isomorphism, and the action of
`GL(n, ℝ)` on `Ω(ℝⁿ)` is `sg ∘ det`.

All of the claim is proved here.

Formalisation. The groupoid is that of finite-dimensional real vector spaces in `Type` and
their linear isomorphisms; `Theory` carries `Ω`, its action `map` (functorial), `card`
(`Nat.card (Ω V) = 2`), `zero : Ω(ℝ⁰) ≃ ℤˣ`, and `St W H` for `IsHalfSpace W H` (a nonzero
linear form `f` with `ker f = W` and `H = {f ≥ 0}`; the opposite half-space is `-H`). The
naturality of `St` is stated for every isomorphism `e : V ≃ V₂` carrying `(W, H)` to
`(W₂, H₂)`, with the restriction `e.ofSubmodules`. The axiom `St_{-H} = τ ∘ St_H` is stated
as `St_{-H} ω ≠ St_H ω`, which on a two-element set is the same. A morphism (`Hom`) is a
natural transformation compatible with `zero` and `St`.

* `Hom.bijective`, `Hom.isIso`: Theorem a) — every morphism is an isomorphism, its inverse
  being a morphism (page 49; induction on the dimension through the Stokes maps).
* `Hom.ext_app`: uniqueness in b) (page 49).
* `canonical`, `exists_unique_hom`: b) — between two theories there is exactly one morphism.
* `Theory.fixes_iff_det_pos`, `Theory.map_eq_iff_det_pos`, `Theory.map_ne_iff_det_neg`:
  page 51 — `g ∈ GL(n, ℝ)` fixes `Ω(ℝⁿ)` iff `det g > 0` and acts by `τ` iff `det g < 0`;
  `Theory.fixes_iff_det_pos'` on any `V`.

The step « de proche en proche » of page 51 is supplied by mathlib's induction principle for
invertible matrices (`Matrix.diagonal_transvection_induction_of_det_ne_zero`): a transvection
is the square of a transvection and a positive diagonal matrix is a square, so they act
trivially on a two-element set; `diag(1, …, 1, −1)` acts by `τ` by the axiom on opposite
half-spaces (`Theory.not_fixes_reflect`), and the other `diag(…, −1, …)` are its conjugates by
permutations. The existence in b) follows the reduction of page 51: reference elements
`r_n ∈ Ω(ℝⁿ)` with `s_{n+1}(r_{n+1}) = r_n` for the half-space `ℝⁿ × ℝ₊`, the bijection
`ψ_n` with `r_n ↦ r′_n`, which commutes with `GL(n, ℝ)` because both actions are `sg ∘ det`,
transported to every `V` by a chart (`phi_eq`: independent of the chart). Existence of a
theory, c), is not part of the claim and is not proved.

What the formalisation found: the bijectivity of the Stokes maps is used as an axiom, as the
reading says (the cardinality argument of page 49 would not give it). Theorem a) and the
uniqueness in b) use neither the axiom on opposite half-spaces nor the naturality of `St`, only
the bijectivity of `St`, the compatibilities of a morphism and `Ω(0) ≃ {±1}`; the axiom on
opposite half-spaces is used only for existence, through the action of `diag(1, …, 1, −1)`.
-/

open Module Pointwise

namespace Grothendieck.Folder68

/-! ## Two-element sets -/

section TwoElements

variable {P Q : Type*}

theorem two_elem (hP : Nat.card P = 2) {a b c : P} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' c).1 hP
  exact (hy a ha).trans (hy b hb).symm

open scoped Classical in
/-- The other element of a two-element set: `τ_P x`. -/
noncomputable def other (x : P) : P := if h : ∃ y, y ≠ x then h.choose else x

theorem other_ne (hP : Nat.card P = 2) (x : P) : other x ≠ x := by
  have h : ∃ y, y ≠ x := ((Nat.card_eq_two_iff' x).1 hP).exists
  rw [other, dite_eq_left h]
  exact h.choose_spec

theorem eq_other (hP : Nat.card P = 2) {x y : P} (h : y ≠ x) : y = other x :=
  two_elem hP h (other_ne hP x)

/-- Two injective maps into a two-element set that agree at one point agree. -/
theorem eq_of_inj_of_eq (hQ : Nat.card Q = 2) {f g : P → Q} (hf : Function.Injective f)
    (hg : Function.Injective g) {x₀ : P} (h : f x₀ = g x₀) : f = g := by
  funext y
  by_cases hy : y = x₀
  · rw [hy, h]
  · exact two_elem hQ (fun e => hy (hf (e.trans h.symm))) (fun e => hy (hg e))

/-- A bijection of a two-element set fixes every point or none. -/
theorem fix_all_or_none (hP : Nat.card P = 2) {σ : P → P} (hσ : Function.Injective σ) :
    (∀ x, σ x = x) ∨ ∀ x, σ x ≠ x := by
  by_contra! h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  have hxy : x ≠ y := fun e => hx (e ▸ hy)
  exact hx (two_elem hP (fun e => hxy (hσ (e.trans hy.symm))) hxy)

end TwoElements


/-! ## The axioms (page 49) -/

/-- `H` is a closed half-space of `V` bounded by the hyperplane `W`: there is a nonzero
linear form `f` with kernel `W` and `H = {f ≥ 0}`. The opposite half-space is `-H`. -/
def IsHalfSpace {V : Type*} [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V) (H : Set V) :
    Prop :=
  ∃ f : V →ₗ[ℝ] ℝ, LinearMap.ker f = W ∧ f ≠ 0 ∧ H = {v | 0 ≤ f v}

theorem IsHalfSpace.neg {V : Type*} [AddCommGroup V] [Module ℝ V] {W : Submodule ℝ V}
    {H : Set V} (h : IsHalfSpace W H) : IsHalfSpace W (-H) := by
  obtain ⟨f, hk, hf, rfl⟩ := h
  refine ⟨-f, by rw [LinearMap.ker_neg, hk], neg_ne_zero.2 hf, ?_⟩
  ext v
  simp

/-- A *theory of orientation* (page 49): a functor `Ω` from the groupoid of finite-dimensional
real vector spaces (in `Type`) and their linear isomorphisms to two-element sets (a), an
identification `Ω(0) ≃ {±1}` (b), and for every hyperplane `W ⊂ V` and closed half-space `H`
bounded by `W` a Stokes map `St_H : Ω(V) → Ω(W)` (c), natural in `(V, H)`, subject to the two
axioms: `St_H` is bijective, and `St_{-H} = τ ∘ St_H`, which on a two-element set says
`St_{-H} ω ≠ St_H ω`. -/
structure Theory where
  /-- The two-element set `Ω(V)`. -/
  Ω : (V : Type) → [AddCommGroup V] → [Module ℝ V] → [FiniteDimensional ℝ V] → Type
  /-- The action of linear isomorphisms. -/
  map : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂], (V ≃ₗ[ℝ] V₂) → Ω V → Ω V₂
  map_refl : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : Ω V),
    map (LinearEquiv.refl ℝ V) ω = ω
  map_trans : ∀ {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
    [AddCommGroup V₃] [Module ℝ V₃] [FiniteDimensional ℝ V₃]
    (e₁ : V₁ ≃ₗ[ℝ] V₂) (e₂ : V₂ ≃ₗ[ℝ] V₃) (ω : Ω V₁), map (e₁.trans e₂) ω = map e₂ (map e₁ ω)
  card : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V], Nat.card (Ω V) = 2
  /-- `Ω(0) ≃ {±1}`. -/
  zero : Ω (Fin 0 → ℝ) ≃ ℤˣ
  /-- The Stokes map of a half-space. -/
  St : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V), IsHalfSpace W H → Ω V → Ω W
  St_natural : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂] (e : V ≃ₗ[ℝ] V₂)
    (W : Submodule ℝ V) (W₂ : Submodule ℝ V₂) (H : Set V) (H₂ : Set V₂)
    (hH : IsHalfSpace W H) (hH₂ : IsHalfSpace W₂ H₂) (hW : W.map (e : V →ₗ[ℝ] V₂) = W₂)
    (_ : e '' H = H₂) (ω : Ω V),
    St W₂ H₂ hH₂ (map e ω) = map (e.ofSubmodules W W₂ hW) (St W H hH ω)
  St_bijective : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H), Function.Bijective (St W H hH)
  St_neg : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H) (hH' : IsHalfSpace W (-H))
    (ω : Ω V), St W (-H) hH' ω ≠ St W H hH ω

/-- A morphism of theories: a natural transformation compatible with b) and c). -/
structure Hom (T T' : Theory) where
  app : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V], T.Ω V → T'.Ω V
  natural : ∀ {V V₂ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂] (e : V ≃ₗ[ℝ] V₂) (ω : T.Ω V),
    app V₂ (T.map e ω) = T'.map e (app V ω)
  zero : ∀ ω, T'.zero (app _ ω) = T.zero ω
  stokes : ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (W : Submodule ℝ V) (H : Set V) (hH : IsHalfSpace W H) (ω : T.Ω V),
    T'.St W H hH (app V ω) = app W (T.St W H hH ω)

namespace Theory

variable (T : Theory)
variable {V V₂ V₃ : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
  [AddCommGroup V₃] [Module ℝ V₃] [FiniteDimensional ℝ V₃]

@[simp] theorem map_symm_map (e : V ≃ₗ[ℝ] V₂) (ω : T.Ω V) : T.map e.symm (T.map e ω) = ω := by
  rw [← T.map_trans, LinearEquiv.self_trans_symm, T.map_refl]

@[simp] theorem map_map_symm (e : V ≃ₗ[ℝ] V₂) (ω : T.Ω V₂) : T.map e (T.map e.symm ω) = ω := by
  rw [← T.map_trans, LinearEquiv.symm_trans_self, T.map_refl]

theorem map_injective (e : V ≃ₗ[ℝ] V₂) : Function.Injective (T.map e) := fun a b h => by
  rw [← T.map_symm_map e a, h, T.map_symm_map]

theorem nonempty (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    Nonempty (T.Ω V) :=
  (Nat.card_pos_iff.1 (by simp [T.card V])).1

/-- `e` acts trivially on `Ω(V)`. -/
def Fixes (e : V ≃ₗ[ℝ] V) : Prop := ∀ ω : T.Ω V, T.map e ω = ω

theorem fixes_or (e : V ≃ₗ[ℝ] V) : T.Fixes e ∨ ∀ ω, T.map e ω ≠ ω :=
  fix_all_or_none (T.card V) (T.map_injective e)

theorem not_fixes_iff (e : V ≃ₗ[ℝ] V) : ¬ T.Fixes e ↔ ∀ ω, T.map e ω ≠ ω := by
  refine ⟨fun h => (T.fixes_or e).resolve_left h, fun h hf => ?_⟩
  obtain ⟨ω⟩ := T.nonempty V
  exact h ω (hf ω)

theorem fixes_refl : T.Fixes (LinearEquiv.refl ℝ V) := T.map_refl

theorem fixes_trans_iff (e₁ e₂ : V ≃ₗ[ℝ] V) :
    T.Fixes (e₁.trans e₂) ↔ (T.Fixes e₁ ↔ T.Fixes e₂) := by
  have hc := T.card V
  have nf := fun e => (T.not_fixes_iff (V := V) e).2
  rcases T.fixes_or e₁ with h₁ | h₁ <;> rcases T.fixes_or e₂ with h₂ | h₂
  · exact iff_of_true (fun ω => by rw [T.map_trans, h₁, h₂]) (iff_of_true h₁ h₂)
  · exact iff_of_false (nf _ fun ω => by rw [T.map_trans, h₁]; exact h₂ ω)
      (fun h => nf _ h₂ (h.1 h₁))
  · exact iff_of_false (nf _ fun ω => by rw [T.map_trans, h₂]; exact h₁ ω)
      (fun h => nf _ h₁ (h.2 h₂))
  · refine iff_of_true (fun ω => ?_) (iff_of_false (nf _ h₁) (nf _ h₂))
    rw [T.map_trans]
    exact two_elem hc (h₂ _) (h₁ ω).symm


theorem fixes_sq (e : V ≃ₗ[ℝ] V) : T.Fixes (e.trans e) :=
  (T.fixes_trans_iff e e).2 Iff.rfl

theorem fixes_conj_iff (q : V ≃ₗ[ℝ] V₂) (e : V₂ ≃ₗ[ℝ] V₂) :
    T.Fixes (q.trans (e.trans q.symm)) ↔ T.Fixes e := by
  constructor
  · intro h ω
    have := h (T.map q.symm ω)
    rw [T.map_trans, T.map_trans, T.map_map_symm] at this
    exact T.map_injective q.symm this
  · intro h ω
    rw [T.map_trans, T.map_trans, h, T.map_symm_map]

end Theory

/-! ## The standard half-space of `ℝ^{m+1}` -/

/-- `ℝⁿ`. -/
abbrev E (n : ℕ) := Fin n → ℝ

/-- The last coordinate. -/
def lastForm (m : ℕ) : E (m + 1) →ₗ[ℝ] ℝ := LinearMap.proj (Fin.last m)

/-- The hyperplane `ℝ^m × 0`. -/
def Wstd (m : ℕ) : Submodule ℝ (E (m + 1)) := LinearMap.ker (lastForm m)

/-- The half-space `ℝ^m × ℝ₊` (the margin of page 51). -/
def Hstd (m : ℕ) : Set (E (m + 1)) := {v | 0 ≤ v (Fin.last m)}

theorem lastForm_ne_zero (m : ℕ) : lastForm m ≠ 0 := fun h => by
  have := LinearMap.congr_fun h (Pi.single (Fin.last m) 1)
  simp [lastForm] at this

theorem isHalfSpace_std (m : ℕ) : IsHalfSpace (Wstd m) (Hstd m) :=
  ⟨lastForm m, rfl, lastForm_ne_zero m, rfl⟩

theorem mem_Wstd {m : ℕ} {v : E (m + 1)} : v ∈ Wstd m ↔ v (Fin.last m) = 0 := Iff.rfl

/-- `ℝ^m × 0 ≃ ℝ^m`. -/
def jStd (m : ℕ) : Wstd m ≃ₗ[ℝ] E m where
  toFun w := fun i => (w : E (m + 1)) i.castSucc
  invFun u := ⟨(Fin.snoc u (0 : ℝ) : E (m + 1)), by simp [mem_Wstd]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv w := by
    refine Subtype.ext (funext fun j => ?_)
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      exact (mem_Wstd.1 w.2).symm
    · simp
  right_inv u := by
    funext i
    simp

namespace Theory

variable (T : Theory)

/-- The Stokes bijection `s_{m+1} : ω_{m+1} → ω_m` of page 51. -/
noncomputable def sStd (m : ℕ) : T.Ω (E (m + 1)) → T.Ω (E m) :=
  fun ω => T.map (jStd m) (T.St (Wstd m) (Hstd m) (isHalfSpace_std m) ω)

theorem sStd_injective (m : ℕ) : Function.Injective (T.sStd m) :=
  (T.map_injective _).comp (T.St_bijective _ _ _).1

theorem sStd_surjective (m : ℕ) : Function.Surjective (T.sStd m) := fun x => by
  obtain ⟨ω, hω⟩ := (T.St_bijective (Wstd m) (Hstd m) (isHalfSpace_std m)).2
    (T.map (jStd m).symm x)
  exact ⟨ω, by simp [sStd, hω]⟩

/-- The reflection `diag(1, …, 1, −1)` acts nontrivially: this is where the axiom
`St_{-H} = τ ∘ St_H` enters. -/
theorem not_fixes_reflect (m : ℕ) (e : E (m + 1) ≃ₗ[ℝ] E (m + 1))
    (he : ∀ v, e v = Function.update v (Fin.last m) (-(v (Fin.last m)))) : ¬ T.Fixes e := by
  have hee : ∀ v, e (e v) = v := fun v => by
    funext j
    rw [he, he]
    by_cases hj : j = Fin.last m
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have hfix : ∀ w ∈ Wstd m, e w = w := fun w hw => by
    rw [he, mem_Wstd.1 hw, neg_zero, ← mem_Wstd.1 hw, Function.update_eq_self]
  have hW : (Wstd m).map (e : E (m + 1) →ₗ[ℝ] E (m + 1)) = Wstd m := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [LinearEquiv.coe_coe, hfix w hw]
      exact hw
    · intro hv
      exact ⟨v, hv, hfix v hv⟩
  have hH : e '' Hstd m = -Hstd m := by
    ext v
    simp only [Set.mem_image, Set.mem_neg, Hstd, Set.mem_ofPred_eq, Pi.neg_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [he] using hw
    · intro hv
      exact ⟨e v, by simpa [he] using hv, hee v⟩
  have hrefl : e.ofSubmodules (Wstd m) (Wstd m) hW = LinearEquiv.refl ℝ _ := by
    ext w
    simp [hfix w w.2]
  intro hf
  obtain ⟨ω⟩ := T.nonempty (E (m + 1))
  have h1 := T.St_natural e (Wstd m) (Wstd m) (Hstd m) (-Hstd m) (isHalfSpace_std m)
    (isHalfSpace_std m).neg hW hH ω
  rw [hf ω, hrefl, T.map_refl] at h1
  exact T.St_neg _ _ _ _ ω h1

end Theory


/-! ## The action of `GL(n, ℝ)` is `sg ∘ det` (page 51) -/

theorem exists_equiv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.det ≠ 0) :
    ∃ e : E n ≃ₗ[ℝ] E n, (e : E n →ₗ[ℝ] E n) = Matrix.toLin' M :=
  ⟨(Matrix.toLin' M).equivOfDetNeZero (by rwa [LinearMap.det_toLin']),
    LinearEquiv.coe_ofIsUnitDet _⟩

theorem iff_mul_pos {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : ((0 < b ↔ 0 < a) ↔ 0 < a * b) := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · simp [not_lt.2 ha.le, not_lt.2 hb.le, mul_pos_of_neg_of_neg ha hb]
  · simp [not_lt.2 ha.le, hb, (mul_neg_of_neg_of_pos ha hb).not_gt]
  · simp [not_lt.2 hb.le, ha, (mul_neg_of_pos_of_neg ha hb).not_gt]
  · simp [ha, hb, mul_pos ha hb]

namespace Theory

variable (T : Theory)

/-- Every isomorphism of matrix `M` acts trivially on `Ω(ℝⁿ)` iff `det M > 0`. -/
def Good (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ e : E n ≃ₗ[ℝ] E n, (e : E n →ₗ[ℝ] E n) = Matrix.toLin' M → (T.Fixes e ↔ 0 < M.det)

variable {n : ℕ}

theorem good_mul {A B : Matrix (Fin n) (Fin n) ℝ} (hA0 : A.det ≠ 0) (hB0 : B.det ≠ 0)
    (hA : T.Good n A) (hB : T.Good n B) : T.Good n (A * B) := by
  intro e he
  obtain ⟨eA, heA⟩ := exists_equiv A hA0
  obtain ⟨eB, heB⟩ := exists_equiv B hB0
  have : e = eB.trans eA := LinearEquiv.toLinearMap_injective (by
    rw [he, LinearEquiv.coe_trans, heA, heB, Matrix.toLin'_mul])
  rw [this, T.fixes_trans_iff, hA eA heA, hB eB heB, Matrix.det_mul]
  exact iff_mul_pos hA0 hB0

theorem good_sq {A : Matrix (Fin n) (Fin n) ℝ} (hA0 : A.det ≠ 0) : T.Good n (A * A) := by
  intro e he
  obtain ⟨eA, heA⟩ := exists_equiv A hA0
  have : e = eA.trans eA := LinearEquiv.toLinearMap_injective (by
    rw [he, LinearEquiv.coe_trans, heA, Matrix.toLin'_mul])
  rw [this, Matrix.det_mul]
  exact iff_of_true (T.fixes_sq eA) (mul_self_pos.2 hA0)

theorem good_one : T.Good n 1 := by
  intro e he
  have : e = LinearEquiv.refl ℝ _ := LinearEquiv.toLinearMap_injective (by
    rw [he, Matrix.toLin'_one]; rfl)
  rw [this, Matrix.det_one]
  exact iff_of_true T.fixes_refl one_pos

theorem good_transvection (t : Matrix.TransvectionStruct (Fin n) ℝ) : T.Good n t.toMatrix := by
  have h : t.toMatrix = Matrix.transvection t.i t.j (t.c / 2) *
      Matrix.transvection t.i t.j (t.c / 2) := by
    rw [Matrix.transvection_mul_transvection_same t.i t.j t.hij, add_halves]; rfl
  rw [h]
  exact T.good_sq (by rw [Matrix.det_transvection_of_ne t.i t.j t.hij]; exact one_ne_zero)

theorem det_diag_ne {D : Fin n → ℝ} (h : ∀ i, D i ≠ 0) : (Matrix.diagonal D).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => h i

theorem update_ne {i : Fin n} {c : ℝ} (hc : c ≠ 0) (j : Fin n) :
    Function.update (1 : Fin n → ℝ) i c j ≠ 0 := by
  by_cases hj : j = i
  · subst hj; simpa using hc
  · simp [Function.update_of_ne hj]

theorem good_reflect (i : Fin n) : T.Good n (Matrix.diagonal (Function.update 1 i (-1))) := by
  intro e he
  have hdet : (Matrix.diagonal (Function.update (1 : Fin n → ℝ) i (-1))).det = -1 := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  rw [hdet]
  refine iff_of_false ?_ (by norm_num)
  have hev : ∀ w : E n, ∀ j, e w j = Function.update (1 : Fin n → ℝ) i (-1) j * w j := by
    intro w j
    have := LinearMap.congr_fun he w
    simp only [LinearEquiv.coe_coe] at this
    rw [this, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  let σ := Equiv.swap i (Fin.last m)
  let q := LinearEquiv.funCongrLeft ℝ ℝ σ
  rw [← T.fixes_conj_iff q e]
  apply T.not_fixes_reflect m
  intro v
  funext j
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_symm, q,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, hev, σ, Equiv.symm_swap]
  by_cases hj : j = Fin.last m
  · subst hj
    simp
  · rw [Function.update_of_ne hj, Equiv.swap_apply_self, Function.update_of_ne, Pi.one_apply, one_mul]
    intro h
    exact hj ((Equiv.swap_apply_eq_iff).1 h |>.trans (Equiv.swap_apply_left _ _))


theorem good_single (i : Fin n) {c : ℝ} (hc : c ≠ 0) :
    T.Good n (Matrix.diagonal (Function.update 1 i c)) := by
  have hpos : ∀ {d : ℝ}, 0 < d → T.Good n (Matrix.diagonal (Function.update 1 i d)) := by
    intro d hd
    have hsq : Matrix.diagonal (Function.update (1 : Fin n → ℝ) i d) =
        Matrix.diagonal (Function.update 1 i (Real.sqrt d)) *
          Matrix.diagonal (Function.update 1 i (Real.sqrt d)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [Real.mul_self_sqrt hd.le]
      · simp [Function.update_of_ne hj]
    rw [hsq]
    exact T.good_sq (det_diag_ne (update_ne (Real.sqrt_pos.2 hd).ne'))
  rcases hc.lt_or_gt with hc | hc
  · have h : Matrix.diagonal (Function.update (1 : Fin n → ℝ) i c) =
        Matrix.diagonal (Function.update 1 i (-c)) *
          Matrix.diagonal (Function.update 1 i (-1)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h]
    exact T.good_mul (det_diag_ne (update_ne (neg_ne_zero.2 hc.ne)))
      (det_diag_ne (update_ne (by norm_num))) (hpos (neg_pos.2 hc)) (T.good_reflect i)
  · exact hpos hc

theorem good_diag {D : Fin n → ℝ} (hD : ∀ i, D i ≠ 0) : T.Good n (Matrix.diagonal D) := by
  classical
  have key : ∀ s : Finset (Fin n),
      T.Good n (Matrix.diagonal fun j => if j ∈ s then D j else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using T.good_one
    | insert i s hi ih =>
      have h : (Matrix.diagonal fun j => if j ∈ insert i s then D j else 1) =
          (Matrix.diagonal fun j => if j ∈ s then D j else 1) *
            Matrix.diagonal (Function.update 1 i (D i)) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      rw [h]
      have hne : ∀ j, (if j ∈ s then D j else 1) ≠ 0 := fun j => by
        split_ifs <;> simp [hD]
      exact T.good_mul (det_diag_ne hne) (det_diag_ne (update_ne (hD i))) ih
        (T.good_single i (hD i))
  simpa using key Finset.univ

theorem good_of_det_ne {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.det ≠ 0) : T.Good n M :=
  Matrix.diagonal_transvection_induction_of_det_ne_zero (T.Good n) M hM
    (fun D hD => T.good_diag fun i h => hD (by
      rw [Matrix.det_diagonal]; exact Finset.prod_eq_zero (Finset.mem_univ i) h))
    T.good_transvection (fun _ _ hA hB => T.good_mul hA hB)

/-- **Page 51.** `g ∈ GL(n, ℝ)` acts trivially on `Ω(ℝⁿ)` iff `det g > 0`. -/
theorem fixes_iff_det_pos (g : E n ≃ₗ[ℝ] E n) :
    T.Fixes g ↔ 0 < LinearMap.det (g : E n →ₗ[ℝ] E n) := by
  have h0 : LinearMap.det (g : E n →ₗ[ℝ] E n) ≠ 0 := g.isUnit_det'.ne_zero
  rw [← LinearMap.det_toMatrix'] at h0 ⊢
  exact T.good_of_det_ne h0 g (Matrix.toLin'_toMatrix' _).symm

/-- **Page 51, the action is `sg ∘ det`**: for every `ω ∈ Ω(ℝⁿ)`, `g ω = ω` if `det g > 0` and
`g ω = τ ω` (that is, `g ω ≠ ω`) if `det g < 0`. -/
theorem map_eq_iff_det_pos (g : E n ≃ₗ[ℝ] E n) (ω : T.Ω (E n)) :
    T.map g ω = ω ↔ 0 < LinearMap.det (g : E n →ₗ[ℝ] E n) := by
  rw [← T.fixes_iff_det_pos]
  exact ⟨fun h => (T.fixes_or g).resolve_right fun hf => hf ω h, fun h => h ω⟩

theorem map_ne_iff_det_neg (g : E n ≃ₗ[ℝ] E n) (ω : T.Ω (E n)) :
    T.map g ω ≠ ω ↔ LinearMap.det (g : E n →ₗ[ℝ] E n) < 0 := by
  have h0 : LinearMap.det (g : E n →ₗ[ℝ] E n) ≠ 0 := g.isUnit_det'.ne_zero
  rw [Ne, T.map_eq_iff_det_pos, not_lt]
  exact h0.le_iff_lt

/-- The same on any finite-dimensional `V`: an automorphism acts trivially on `Ω(V)` iff its
determinant is positive. -/
theorem fixes_iff_det_pos' {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (g : V ≃ₗ[ℝ] V) : T.Fixes g ↔ 0 < LinearMap.det (g : V →ₗ[ℝ] V) := by
  let c : V ≃ₗ[ℝ] E (finrank ℝ V) := (Module.finBasis ℝ V).equivFun
  rw [← T.fixes_conj_iff c.symm g, T.fixes_iff_det_pos, ← LinearMap.det_conj (g : V →ₗ[ℝ] V) c]
  rfl

/-- The reference elements `r_n ∈ ω_n`: `r_0 = 1` and `s_{n+1}(r_{n+1}) = r_n`. -/
noncomputable def ref : (n : ℕ) → T.Ω (E n)
  | 0 => T.zero.symm 1
  | m + 1 => Function.surjInv (T.sStd_surjective m) (ref m)

theorem ref_zero : T.ref 0 = T.zero.symm 1 := rfl

theorem sStd_ref (m : ℕ) : T.sStd m (T.ref (m + 1)) = T.ref m :=
  Function.surjInv_eq _ _

end Theory

/-! ## Hyperplanes and adapted charts -/

theorem exists_halfSpace (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {m : ℕ} (h : finrank ℝ V = m + 1) :
    ∃ (W : Submodule ℝ V) (H : Set V), IsHalfSpace W H ∧ finrank ℝ W = m := by
  let c : V ≃ₗ[ℝ] E (m + 1) := LinearEquiv.ofFinrankEq V (E (m + 1)) (by simp [h])
  let f : V →ₗ[ℝ] ℝ := lastForm m ∘ₗ (c : V →ₗ[ℝ] E (m + 1))
  have hf : f ≠ 0 := fun hf => lastForm_ne_zero m (LinearMap.ext fun v => by
    have := LinearMap.congr_fun hf (c.symm v)
    simpa [f] using this)
  refine ⟨LinearMap.ker f, {v | 0 ≤ f v}, ⟨f, rfl, hf, rfl⟩, ?_⟩
  have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  omega

/-- Every half-space is carried to the standard one `ℝ^m × ℝ₊` by some isomorphism. -/
theorem exists_adapted {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {W : Submodule ℝ V} {H : Set V} (hH : IsHalfSpace W H) :
    ∃ m, ∃ c : V ≃ₗ[ℝ] E (m + 1),
      W.map (c : V →ₗ[ℝ] E (m + 1)) = Wstd m ∧ c '' H = Hstd m := by
  obtain ⟨f, rfl, hf, rfl⟩ := hH
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  set m := finrank ℝ (LinearMap.ker f)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := DFunLike.ne_iff.1 hf
  set v₀ := (f v)⁻¹ • v
  have hv₀ : f v₀ = 1 := by simp [v₀, hv]
  let jW : LinearMap.ker f ≃ₗ[ℝ] E m := LinearEquiv.ofFinrankEq _ _ (by simp [m])
  let init : E (m + 1) →ₗ[ℝ] E m := LinearMap.pi fun i => LinearMap.proj i.castSucc
  let d : E (m + 1) →ₗ[ℝ] V := (LinearMap.ker f).subtype ∘ₗ (jW.symm : E m →ₗ[ℝ] _) ∘ₗ init +
    LinearMap.toSpanSingleton ℝ V v₀ ∘ₗ lastForm m
  have hfd : ∀ u, f (d u) = u (Fin.last m) := fun u => by
    have h1 : f ((jW.symm (init u) : LinearMap.ker f) : V) = 0 := (jW.symm (init u)).2
    simp [d, lastForm, h1, hv₀]
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hl : u (Fin.last m) = 0 := by rw [← hfd u, hu, map_zero]
    have h2 : init u = 0 := by
      have : ((jW.symm (init u) : LinearMap.ker f) : V) = 0 := by
        simpa [d, lastForm, hl] using hu
      have : jW.symm (init u) = 0 := Subtype.ext this
      simpa using congrArg jW this
    exact funext fun j => Fin.lastCases hl (fun i => congrFun h2 i) j
  have hbij : Function.Bijective d :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [← hdim])).1 hinj⟩
  let c : V ≃ₗ[ℝ] E (m + 1) := (LinearEquiv.ofBijective d hbij).symm
  have hdc : ∀ x, d (c x) = x := fun x => (LinearEquiv.ofBijective d hbij).apply_symm_apply x
  have key : ∀ x, c x (Fin.last m) = f x := fun x => by rw [← hfd (c x), hdc]
  refine ⟨m, c, ?_, ?_⟩
  · ext u
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, LinearMap.mem_ker, mem_Wstd]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [key, hx]
    · intro hu
      exact ⟨c.symm u, by rw [← key, c.apply_symm_apply, hu], c.apply_symm_apply u⟩
  · ext u
    simp only [Set.mem_image, Hstd, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [key]; exact hx
    · intro hu
      exact ⟨c.symm u, by show 0 ≤ f _; rw [← key, c.apply_symm_apply]; exact hu,
        c.apply_symm_apply u⟩

/-! ## Theorem of page 49, a) and uniqueness in b) -/

namespace Hom

variable {T T' : Theory}

/-- Theorem a), first half: the components of a morphism are injective (induction on the
dimension through the Stokes maps). -/
theorem injective (φ : Hom T T') : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V], finrank ℝ V = n → Function.Injective (φ.app V) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ h a b hab
    let c : V ≃ₗ[ℝ] E 0 := LinearEquiv.ofFinrankEq V (E 0) (by simp [h])
    have := congrArg (fun x => T'.zero (T'.map c x)) hab
    simp only [← φ.natural, φ.zero] at this
    exact T.map_injective c (T.zero.injective this)
  | succ m ih =>
    intro V _ _ _ h a b hab
    obtain ⟨W, H, hH, hW⟩ := exists_halfSpace V h
    have := congrArg (T'.St W H hH) hab
    rw [φ.stokes, φ.stokes] at this
    exact (T.St_bijective W H hH).1 (ih W hW this)

/-- **Theorem a)** (page 49): every component of a morphism of theories is bijective. -/
theorem bijective (φ : Hom T T') (V : Type) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] : Function.Bijective (φ.app V) := by
  have : Finite (T'.Ω V) := Nat.finite_of_card_ne_zero (by rw [T'.card]; norm_num)
  exact (φ.injective _ V rfl).bijective_of_nat_card_le (by rw [T.card, T'.card])

/-- **Uniqueness in b)** (page 49): two morphisms of theories are equal. -/
theorem ext_app (φ ψ : Hom T T') : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V], finrank ℝ V = n → φ.app V = ψ.app V := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ h
    funext a
    let c : V ≃ₗ[ℝ] E 0 := LinearEquiv.ofFinrankEq V (E 0) (by simp [h])
    apply T'.map_injective c
    apply T'.zero.injective
    rw [← φ.natural, ← ψ.natural, φ.zero, ψ.zero]
  | succ m ih =>
    intro V _ _ _ h
    funext a
    obtain ⟨W, H, hH, hW⟩ := exists_halfSpace V h
    apply (T'.St_bijective W H hH).1
    rw [φ.stokes, ψ.stokes, ih W hW]

/-- The identity morphism. -/
def id (T : Theory) : Hom T T where
  app _ _ _ _ ω := ω
  natural _ _ := rfl
  zero _ := rfl
  stokes _ _ _ _ := rfl

/-- Composition of morphisms. -/
def comp {T'' : Theory} (ψ : Hom T' T'') (φ : Hom T T') : Hom T T'' where
  app V _ _ _ ω := ψ.app V (φ.app V ω)
  natural e ω := by rw [φ.natural, ψ.natural]
  zero ω := by rw [ψ.zero, φ.zero]
  stokes W H hH ω := by rw [ψ.stokes, φ.stokes]

end Hom

/-! ## Existence in b): the comparison of two theories -/

section Construction

variable (T T' : Theory)

open scoped Classical in
/-- `ψ_n : ω_n → ω'_n`, the bijection with `r_n ↦ r'_n`. -/
noncomputable def psi (n : ℕ) (ω : T.Ω (E n)) : T'.Ω (E n) :=
  if ω = T.ref n then T'.ref n else other (T'.ref n)

variable {T T'}

theorem psi_ref (n : ℕ) : psi T T' n (T.ref n) = T'.ref n := by simp [psi]

theorem psi_injective (n : ℕ) : Function.Injective (psi T T' n) := by
  intro a b h
  by_contra hab
  by_cases ha : a = T.ref n
  · have hb : b ≠ T.ref n := fun hb => hab (ha.trans hb.symm)
    simp only [psi, ha, hb, ite_true, ite_false] at h
    exact other_ne (T'.card _) _ h.symm
  · by_cases hb : b = T.ref n
    · simp only [psi, ha, hb, ite_true, ite_false] at h
      exact other_ne (T'.card _) _ h
    · exact hab (two_elem (T.card _) ha hb)

theorem psi_map {n : ℕ} (g : E n ≃ₗ[ℝ] E n) (ω : T.Ω (E n)) :
    psi T T' n (T.map g ω) = T'.map g (psi T T' n ω) := by
  rcases T.fixes_or g with h | h
  · have h' : T'.Fixes g := (T'.fixes_iff_det_pos g).2 ((T.fixes_iff_det_pos g).1 h)
    rw [h, h']
  · have h' : ∀ x, T'.map g x ≠ x := (T'.not_fixes_iff g).1 fun hf =>
      (T.not_fixes_iff g).2 h ((T.fixes_iff_det_pos g).2 ((T'.fixes_iff_det_pos g).1 hf))
    exact two_elem (T'.card _) (fun e => h ω (psi_injective n e)) (h' _)

theorem psi_stokes (m : ℕ) (ω : T.Ω (E (m + 1))) :
    T'.sStd m (psi T T' (m + 1) ω) = psi T T' m (T.sStd m ω) :=
  congrFun (eq_of_inj_of_eq (T'.card _) ((T'.sStd_injective m).comp (psi_injective _))
    ((psi_injective _).comp (T.sStd_injective m)) (x₀ := T.ref (m + 1))
    (by simp only [Function.comp, psi_ref, Theory.sStd_ref])) ω

theorem psi_zero (ω : T.Ω (E 0)) : T'.zero (psi T T' 0 ω) = T.zero ω :=
  congrFun (eq_of_inj_of_eq (Q := ℤˣ) (by rw [Nat.card_eq_fintype_card]; rfl)
    (T'.zero.injective.comp (psi_injective _)) T.zero.injective (x₀ := T.ref 0)
    (by
      show T'.zero (psi T T' 0 (T.ref 0)) = T.zero (T.ref 0)
      rw [psi_ref, Theory.ref_zero, Theory.ref_zero]
      simp)) ω

variable (T T')

/-- A chosen chart `V ≃ ℝ^{dim V}`. -/
noncomputable def chart (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    V ≃ₗ[ℝ] E (finrank ℝ V) :=
  (Module.finBasis ℝ V).equivFun

/-- The component on `V` of the comparison morphism. -/
noncomputable def phi (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ω : T.Ω V) : T'.Ω V :=
  T'.map (chart V).symm (psi T T' _ (T.map (chart V) ω))

variable {T T'}

/-- `phi` does not depend on the chart, because `ψ_n` commutes with `GL(n, ℝ)`. -/
theorem phi_eq {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {n : ℕ}
    (c : V ≃ₗ[ℝ] E n) (ω : T.Ω V) : phi T T' V ω = T'.map c.symm (psi T T' n (T.map c ω)) := by
  have h : finrank ℝ V = n := by simpa using c.finrank_eq
  subst h
  set g := c.symm.trans (chart V)
  have hb : chart V = c.trans g := by ext x; simp [g]
  rw [phi, hb, T.map_trans, psi_map, ← T'.map_trans]
  congr 1
  ext x
  simp [g]

variable (T T')

/-- **Existence in b)**: the comparison morphism. -/
noncomputable def canonical : Hom T T' where
  app V _ _ _ := phi T T' V
  natural {V V₂} _ _ _ _ _ _ e ω := by
    have h1 : e.trans (e.symm.trans (chart V)) = chart V := by ext; simp
    have h2 : (e.symm.trans (chart V)).symm = (chart V).symm.trans e := by ext; simp
    rw [phi_eq (e.symm.trans (chart V)), ← T.map_trans, h1, h2, T'.map_trans, phi]
  zero ω := by
    rw [phi_eq (LinearEquiv.refl ℝ (E 0)), T.map_refl, LinearEquiv.refl_symm, T'.map_refl,
      psi_zero]
  stokes {V} _ _ _ W H hH ω := by
    obtain ⟨m, c, hWc, hHc⟩ := exists_adapted hH
    have hWc' : (Wstd m).map (c.symm : E (m + 1) →ₗ[ℝ] V) = W := by
      rw [← hWc, ← Submodule.map_comp]
      ext x
      simp
    have hHc' : c.symm '' Hstd m = H := by
      rw [← hHc, ← Set.image_comp]
      simp
    let cW := c.ofSubmodules W (Wstd m) hWc
    rw [phi_eq c, T'.St_natural c.symm (Wstd m) W (Hstd m) H (isHalfSpace_std m) hH hWc' hHc',
      phi_eq (cW.trans (jStd m))]
    have h1 : ∀ y, T'.St (Wstd m) (Hstd m) (isHalfSpace_std m) y =
        T'.map (jStd m).symm (T'.sStd m y) := fun y => by simp [Theory.sStd]
    have h2 : T.sStd m (T.map c ω) = T.map (cW.trans (jStd m)) (T.St W H hH ω) := by
      rw [Theory.sStd, T.St_natural c W (Wstd m) H (Hstd m) hH (isHalfSpace_std m) hWc hHc,
        T.map_trans]
    have h3 : (jStd m).symm.trans (c.symm.ofSubmodules (Wstd m) W hWc') =
        (cW.trans (jStd m)).symm := by
      ext w
      rfl
    rw [h1, psi_stokes, h2, ← T'.map_trans, h3]

end Construction

/-! ## The theorem of page 49 -/

/-- **Theorem b)** (page 49): between two theories of orientation there is exactly one
morphism, and its components are bijective. -/
theorem exists_unique_hom (T T' : Theory) :
    ∃ φ : Hom T T', (∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
      Function.Bijective (φ.app V)) ∧
      ∀ ψ : Hom T T', ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
        ψ.app V = φ.app V :=
  ⟨canonical T T', fun V _ _ _ => (canonical T T').bijective V,
    fun ψ V _ _ _ => ψ.ext_app _ _ V rfl⟩

/-- **Theorem a)** (page 49), categorically: every morphism of theories is an isomorphism; its
inverse is a morphism of theories. -/
theorem Hom.isIso {T T' : Theory} (φ : Hom T T') :
    ∃ ψ : Hom T' T, (∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
      (ω : T.Ω V), ψ.app V (φ.app V ω) = ω) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ω : T'.Ω V),
        φ.app V (ψ.app V ω) = ω :=
  ⟨canonical T' T,
    fun V _ _ _ ω => congrFun (((canonical T' T).comp φ).ext_app (Hom.id T) _ V rfl) ω,
    fun V _ _ _ ω => congrFun ((φ.comp (canonical T' T)).ext_app (Hom.id T') _ V rfl) ω⟩

end Grothendieck.Folder68
