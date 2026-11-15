module

public import Mathlib
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Projective

@[expose] public section


/-!
# IHÉS FG_IL_5_SGA6_1_5, views 1–5: modules with an `n`-presentation

A first-person typescript of the Fonds Grothendieck–Illusie (IHÉS), §§ 4–7 of a longer text on
finite `n`-presentations. § 4 works in an abelian category `C` with a full subcategory `P` of
projective objects stable under finite sums. Def. 4.1 (view 1): an `n`-presentation of `X` is an
exact sequence `Lₙ → ⋯ → L₀ → X → 0` with the `Lᵢ` in `P`; `Cₙ` is the subcategory of the `X`
that have one, with `Cₙ = C` for `n < 0`; `C₀` are the objects of finite type, `C₁` those of finite
presentation. Prop. 4.2 (view 1): an extension of two objects of `Cₙ` is in `Cₙ`. Cor. 4.3: a
finite sum. Prop. 4.4 (view 2): for `0 → R → M₀ → X → 0` with `M₀ ∈ Cₙ`, `X ∈ Cₙ` iff
`R ∈ Cₙ₋₁`. Cor. 4.7 bis (view 4): a direct factor of an object of `Cₙ` is in `Cₙ`. § 5
(view 5) takes `C` the `A`-modules, `A` not necessarily commutative, `P` the free modules of finite
type, and notes that the `Cₙ` do not change if `P` is the projective modules of finite type.

Here `C` is the category of left modules over a ring `R` and `P` the modules `Fin k → R`.
`IsNPresented R n M` is defined by recursion on `n`, which is the edition's choice (the page
writes the exact sequence): `M` is `0`-presented if it is finite, and `(n+1)`-presented if some
surjection `Rᵏ ↠ M` has an `n`-presented kernel. All modules live in the universe of `R`, so that
the kernels stay in it.

**What is proved.**
* `isNPresented_zero_iff`, `isNPresented_one_iff`: at `n = 0` and `n = 1` the notion is
  `Module.Finite` and `Module.FinitePresentation`.
* `IsNPresented.of_ker_of_surjective`, `IsNPresented.of_exact`: **Prop. 4.2.**
* `IsNPresented.prod`: **Cor. 4.3** for two summands.
* `IsNPresented.iff_ker`, `IsNPresented.iff_of_exact`: **Prop. 4.4**, as on the page.
* `isNPresented_succ_iff_forall`, `isNPresented_succ_iff_exists`: 4.4 with a free module of
  finite type in the middle, for *every* surjection and for *some* surjection (Stacks 064U, 064X).
* `IsNPresented.of_exact_right`, `IsNPresented.of_exact_left`: the two other cases of « two out of
  three » in a short exact sequence (Stacks 064R): `M ∈ Cₙ₊₁, M' ∈ Cₙ ⇒ M'' ∈ Cₙ₊₁`, and
  `M ∈ Cₙ, M'' ∈ Cₙ₊₁ ⇒ M' ∈ Cₙ`. The second is sharper than the « il faut » of 4.4, which asks
  `M ∈ Cₙ₊₁`.
* `IsNPresented.of_retract`: **Cor. 4.7 bis.**
* `IsNPresented.of_free`, `IsNPresented.of_projective`, `IsNPresented.succ_of_projective`: free
  and projective modules of finite type are `n`-presented for all `n`, and § 5's remark that
  projective `Lᵢ` give the same `Cₙ`. `IsNPresented.of_le`: `Cₙ ⊇ Cₙ₊₁`.

The proofs follow the induction of the page in a different order. The page proves 4.2 by the
horseshoe construction of Cartan–Eilenberg V 2.2, and 4.4 by modifying a presentation of `X` until
it maps onto `M₀`. Here one construction serves both (`exists_coprod`): for `p : N ↠ M` and
`u : F ↠ M` with `F` projective, lift `u` to `h : F → N`; then `(a, b) ↦ a + h b` maps
`ker p × F` onto `N` with kernel `ker u`. 4.2 at level `n + 1` follows from the quotient half of
4.4 at level `n + 1`, which needs 4.2 at level `n` only. The « il faut » half of 4.4 comes from
4.2 and 4.7 bis, by the same construction.

**Not formalised.** The abelian-category setting of § 4 (only modules are treated), the
`∞`-presentations and Cor. 4.7 (`C_∞ = ⋂ Cₙ`), Cor. 4.5 and 4.6 (longer exact sequences),
Prop. 4.8 and Cor. 4.9 (exact functors and derived functors), and §§ 5–7 beyond the remark on
projective modules: flat base change, localisation, finite resolutions, regular immersions,
relative `n`-presentation over an algebra, preschemes. Modules in a universe other than that of
`R` are not covered.
-/

namespace Grothendieck.IhesSGA6_1_5

open Function LinearMap

universe u

variable (R : Type u) [Ring R]

/-- `IsNPresented R n M`: `M` has an `n`-presentation, an exact sequence
`Lₙ → ⋯ → L₀ → M → 0` with the `Lᵢ` free of finite type. -/
def IsNPresented : ℕ → (M : Type u) → [AddCommGroup M] → [Module R M] → Prop
  | 0, M, _, _ => Module.Finite R M
  | n + 1, M, _, _ => ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] M), Surjective f ∧ IsNPresented n (ker f)

variable {R}

section

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem isNPresented_zero_iff : IsNPresented R 0 M ↔ Module.Finite R M := Iff.rfl

theorem isNPresented_succ_iff {n : ℕ} : IsNPresented R (n + 1) M ↔
    ∃ (k : ℕ) (f : (Fin k → R) →ₗ[R] M), Surjective f ∧ IsNPresented R n (ker f) := Iff.rfl

theorem IsNPresented.of_equiv {n : ℕ} (e : M ≃ₗ[R] N) (h : IsNPresented R n M) :
    IsNPresented R n N := by
  induction n generalizing M N with
  | zero => have : Module.Finite R M := h; exact Module.Finite.equiv e
  | succ n ih =>
    obtain ⟨k, f, hf, hk⟩ := h
    refine ⟨k, e.toLinearMap ∘ₗ f, e.surjective.comp hf, ih (LinearEquiv.ofEq _ _ ?_) hk⟩
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

theorem IsNPresented.finite {n : ℕ} (h : IsNPresented R n M) : Module.Finite R M := by
  cases n with
  | zero => exact h
  | succ n => obtain ⟨k, f, hf, -⟩ := h; exact Module.Finite.of_surjective f hf

theorem IsNPresented.of_subsingleton [Subsingleton M] (n : ℕ) : IsNPresented R n M := by
  induction n generalizing M with
  | zero => exact Module.Finite.of_finite
  | succ n ih =>
    refine ⟨0, 0, fun y => ⟨0, Subsingleton.elim _ _⟩, ih⟩

theorem IsNPresented.of_succ {n : ℕ} (h : IsNPresented R (n + 1) M) : IsNPresented R n M := by
  induction n generalizing M with
  | zero => exact h.finite
  | succ n ih => obtain ⟨k, f, hf, hk⟩ := h; exact ⟨k, f, hf, ih hk⟩

theorem IsNPresented.of_le {m n : ℕ} (hmn : m ≤ n) (h : IsNPresented R n M) :
    IsNPresented R m M := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

/-- A presentation step may start from any free module of finite type. -/
theorem IsNPresented.succ_of_free {n : ℕ} {F : Type u} [AddCommGroup F] [Module R F]
    [Module.Free R F] [Module.Finite R F] (f : F →ₗ[R] M) (hf : Surjective f)
    (hk : IsNPresented R n (ker f)) : IsNPresented R (n + 1) M := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M; exact .of_subsingleton _
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := F)
  have : Finite ι := Module.Finite.finite_basis b
  let e : F ≃ₗ[R] (Fin (Nat.card ι) → R) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft R R (Finite.equivFin ι).symm)
  refine ⟨_, f ∘ₗ e.symm.toLinearMap, hf.comp e.symm.surjective, hk.of_equiv ?_⟩
  refine (e.submoduleMap (ker f)).trans (LinearEquiv.ofEq _ _ ?_)
  rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]

theorem IsNPresented.of_free [Module.Free R M] [Module.Finite R M] (n : ℕ) :
    IsNPresented R n M := by
  cases n with
  | zero => assumption
  | succ n =>
    refine IsNPresented.succ_of_free LinearMap.id (fun y => ⟨y, rfl⟩) ?_
    rw [LinearMap.ker_id]
    exact .of_subsingleton n

/-- The product of two submodules, as the product of the two modules. -/
def prodEquiv (p : Submodule R M) (q : Submodule R N) : (p × q) ≃ₗ[R] p.prod q where
  toFun x := ⟨(x.1, x.2), x.1.2, x.2.2⟩
  invFun y := (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Cor. 4.3**, two summands: `M × N` is `n`-presented if `M` and `N` are. -/
theorem IsNPresented.prod {n : ℕ} (hM : IsNPresented R n M) (hN : IsNPresented R n N) :
    IsNPresented R n (M × N) := by
  induction n generalizing M N with
  | zero =>
    have : Module.Finite R M := hM
    have : Module.Finite R N := hN
    exact (inferInstance : Module.Finite R (M × N))
  | succ n ih =>
    obtain ⟨a, f, hf, ha⟩ := hM
    obtain ⟨b, g, hg, hb⟩ := hN
    refine IsNPresented.succ_of_free (f.prodMap g) (hf.prodMap hg) ?_
    rw [LinearMap.ker_prodMap]
    exact (ih ha hb).of_equiv (prodEquiv _ _)

end

section

variable {M N F : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup F] [Module R F]

/-- The step shared by 4.2 and 4.4. Given `p : N ↠ M` and `u : F ↠ M` with `F` projective, lift
`u` to `h : F → N`; then `(a, b) ↦ a + h b` is a surjection `ker p × F ↠ N` whose kernel is
isomorphic to `ker u`. -/
theorem exists_coprod [Module.Projective R F] (p : N →ₗ[R] M) (hp : Surjective p)
    (u : F →ₗ[R] M) (hu : Surjective u) :
    ∃ g : (ker p × F) →ₗ[R] N, Surjective g ∧ Nonempty (ker g ≃ₗ[R] ker u) := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property p u hp
  have hh' : ∀ b, p (h b) = u b := fun b => congrArg (· b) hh
  refine ⟨(ker p).subtype.coprod h, fun y => ?_, ⟨LinearEquiv.ofBijective
    (LinearMap.codRestrict (ker u) ((LinearMap.snd R _ F).comp (ker _).subtype) ?_) ⟨?_, ?_⟩⟩⟩
  · obtain ⟨b, hb⟩ := hu (p y)
    refine ⟨(⟨y - h b, ?_⟩, b), ?_⟩
    · simp [mem_ker, hh', hb]
    · simp
  · rintro ⟨⟨a, b⟩, hx⟩
    have hx' : (a : N) + h b = 0 := by simpa using hx
    have := congrArg p hx'
    rw [map_add, a.2, zero_add, hh', map_zero] at this
    exact this
  · rintro ⟨⟨a, b⟩, hx⟩ ⟨⟨a', b'⟩, hx'⟩ hab
    have hb : b = b' := congrArg Subtype.val hab
    subst hb
    have h1 : (a : N) + h b = 0 := by simpa using hx
    have h2 : (a' : N) + h b = 0 := by simpa using hx'
    have : a = a' := Subtype.ext (by rw [eq_neg_of_add_eq_zero_left h1,
      eq_neg_of_add_eq_zero_left h2])
    subst this
    rfl
  · rintro ⟨b, hb⟩
    have hb' : u b = 0 := hb
    refine ⟨⟨(⟨-h b, ?_⟩, b), ?_⟩, rfl⟩
    · simp [mem_ker, hh', hb']
    · simp [mem_ker]

end

section

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The kernel of `p ∘ u`, mapped onto `ker p` by `u`, has kernel `ker u` (when `u` is onto). -/
theorem exists_ker_comp {F : Type u} [AddCommGroup F] [Module R F] (p : N →ₗ[R] M)
    (u : F →ₗ[R] N) (hu : Surjective u) :
    ∃ q : ker (p ∘ₗ u) →ₗ[R] ker p, Surjective q ∧ Nonempty (ker q ≃ₗ[R] ker u) := by
  refine ⟨u.restrict fun x hx => by simpa [mem_ker] using hx, ?_, ⟨LinearEquiv.ofBijective
    (LinearMap.codRestrict (ker u) ((ker (p ∘ₗ u)).subtype.comp (ker _).subtype) ?_) ⟨?_, ?_⟩⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hu y
    exact ⟨⟨x, by simpa [mem_ker] using hy⟩, rfl⟩
  · rintro ⟨x, hx⟩
    have := congrArg Subtype.val (mem_ker.mp hx)
    simpa [mem_ker] using this
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  · rintro ⟨x, hx⟩
    have hx' : u x = 0 := hx
    refine ⟨⟨⟨x, by simp [mem_ker, hx']⟩, ?_⟩, rfl⟩
    exact mem_ker.mpr (Subtype.ext hx')

/-- The quotient step of 4.4 at level `n + 1`, assuming 4.2 at level `n`. -/
theorem quot_succ_aux {n : ℕ}
    (hE : ∀ (N M : Type u) [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
      (p : N →ₗ[R] M), Surjective p → IsNPresented R n (ker p) → IsNPresented R n M →
      IsNPresented R n N)
    (p : N →ₗ[R] M) (hp : Surjective p) (hN : IsNPresented R (n + 1) N)
    (hK : IsNPresented R n (ker p)) : IsNPresented R (n + 1) M := by
  obtain ⟨k, u, hu, hk⟩ := hN
  obtain ⟨q, hq, ⟨e⟩⟩ := exists_ker_comp p u hu
  exact ⟨k, p ∘ₗ u, hp.comp hu, hE _ _ q hq (hk.of_equiv e.symm) hK⟩

/-- **Prop. 4.2** (surjection form): if `0 → ker p → N → M → 0` and `ker p`, `M` are
`n`-presented, so is `N`. -/
theorem IsNPresented.of_ker_of_surjective {n : ℕ} (p : N →ₗ[R] M) (hp : Surjective p)
    (hK : IsNPresented R n (ker p)) (hM : IsNPresented R n M) : IsNPresented R n N := by
  induction n generalizing N M with
  | zero =>
    have : Module.Finite R M := hM
    have : Module.Finite R (ker p) := hK
    obtain ⟨k, u, hu⟩ := Module.Finite.exists_fin' R M
    obtain ⟨g, hg, -⟩ := exists_coprod p hp u hu
    exact Module.Finite.of_surjective g hg
  | succ n ih =>
    obtain ⟨k, u, hu, hk⟩ := hM
    obtain ⟨g, hg, ⟨e⟩⟩ := exists_coprod p hp u hu
    exact quot_succ_aux (fun _ _ _ _ _ _ p hp hK hM => ih p hp hK hM) g hg
      (hK.prod (.of_free _)) (hk.of_equiv e.symm)

/-- **Prop. 4.4, « il suffit »** (surjection form): if `0 → ker p → N → M → 0` with `N`
`(n+1)`-presented and `ker p` `n`-presented, `M` is `(n+1)`-presented. -/
theorem IsNPresented.of_surjective {n : ℕ} (p : N →ₗ[R] M) (hp : Surjective p)
    (hN : IsNPresented R (n + 1) N) (hK : IsNPresented R n (ker p)) :
    IsNPresented R (n + 1) M :=
  quot_succ_aux (fun _ _ _ _ _ _ p hp hK hM => .of_ker_of_surjective p hp hK hM) p hp hN hK

/-- **Cor. 4.7 bis**: a retract (a direct factor) of an `n`-presented module is `n`-presented. -/
theorem IsNPresented.of_retract {n : ℕ} (s : M →ₗ[R] N) (r : N →ₗ[R] M) (hrs : r ∘ₗ s = .id)
    (hN : IsNPresented R n N) : IsNPresented R n M := by
  induction n generalizing M N with
  | zero =>
    have : Module.Finite R N := hN
    exact Module.Finite.of_surjective r fun y => ⟨s y, congrArg (· y) hrs⟩
  | succ n ih =>
    have hrs' : ∀ y, r (s y) = y := fun y => congrArg (· y) hrs
    refine .of_surjective r (fun y => ⟨s y, hrs' y⟩) hN (ih (ker r).subtype
      (LinearMap.codRestrict (ker r) (LinearMap.id - s ∘ₗ r) fun y => by simp [mem_ker, hrs'])
      ?_ hN.of_succ)
    ext ⟨y, hy⟩
    simp [mem_ker.mp hy]

/-- **Prop. 4.4, « il faut »** (surjection form), in the sharper form of Stacks 064R (3): if
`0 → ker p → N → M → 0` with `N` `n`-presented and `M` `(n+1)`-presented, `ker p` is
`n`-presented. -/
theorem IsNPresented.ker_of_surjective {n : ℕ} (p : N →ₗ[R] M) (hp : Surjective p)
    (hN : IsNPresented R n N) (hM : IsNPresented R (n + 1) M) : IsNPresented R n (ker p) := by
  obtain ⟨k, u, hu, hk⟩ := hM
  obtain ⟨g, hg, ⟨e⟩⟩ := exists_coprod p hp u hu
  exact (IsNPresented.of_ker_of_surjective g hg (hk.of_equiv e.symm) hN).of_retract
    (LinearMap.inl R _ _) (LinearMap.fst R _ _) (LinearMap.fst_comp_inl R _ _)

end

section

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Finite projective modules have `n`-presentations for every `n`. -/
theorem IsNPresented.of_projective [Module.Projective R M] [Module.Finite R M] (n : ℕ) :
    IsNPresented R n M := by
  obtain ⟨_, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact (IsNPresented.of_free n).of_retract g f hfg

/-- § 5: the `n`-presented modules do not change if the `Lᵢ` are only required to be projective of
finite type. -/
theorem IsNPresented.succ_of_projective {n : ℕ} {F : Type u} [AddCommGroup F] [Module R F]
    [Module.Projective R F] [Module.Finite R F] (f : F →ₗ[R] M) (hf : Surjective f)
    (hk : IsNPresented R n (ker f)) : IsNPresented R (n + 1) M :=
  .of_surjective f hf (.of_projective _) hk

/-- At `n = 1`, an `n`-presentation is a finite presentation in the sense of mathlib. -/
theorem isNPresented_one_iff : IsNPresented R 1 M ↔ Module.FinitePresentation R M := by
  constructor
  · rintro ⟨k, f, hf, hk⟩
    have : Module.Finite R (ker f) := hk
    exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp this)
  · intro h
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    exact ⟨k, f, hf, Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker f hf)⟩

/-- **Prop. 4.4** with a free module of finite type in the middle (Stacks 064U, 064X): `M` is
`(n+1)`-presented iff it is finite and the kernel of *every* surjection from a free module of
finite type is `n`-presented. -/
theorem isNPresented_succ_iff_forall {n : ℕ} : IsNPresented R (n + 1) M ↔ Module.Finite R M ∧
    ∀ (F : Type u) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
      (f : F →ₗ[R] M), Surjective f → IsNPresented R n (ker f) := by
  refine ⟨fun h => ⟨h.finite, fun F _ _ _ _ f hf => .ker_of_surjective f hf (.of_free n) h⟩,
    fun ⟨_, h⟩ => ?_⟩
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ⟨k, f, hf, h _ f hf⟩

/-- **Prop. 4.4**, the same with *some* surjection. -/
theorem isNPresented_succ_iff_exists {n : ℕ} : IsNPresented R (n + 1) M ↔
    ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F)
      (_ : Module.Finite R F) (f : F →ₗ[R] M), Surjective f ∧ IsNPresented R n (ker f) :=
  ⟨fun ⟨_, f, hf, hk⟩ => ⟨_, _, _, inferInstance, inferInstance, f, hf, hk⟩,
    fun ⟨_, _, _, _, _, f, hf, hk⟩ => .succ_of_free f hf hk⟩

/-- **Prop. 4.4** as on the page (surjection form): if `0 → ker p → N → M → 0` with `N`
`(n+1)`-presented, `M` is `(n+1)`-presented iff `ker p` is `n`-presented. -/
theorem IsNPresented.iff_ker {n : ℕ} (p : N →ₗ[R] M) (hp : Surjective p)
    (hN : IsNPresented R (n + 1) N) :
    IsNPresented R (n + 1) M ↔ IsNPresented R n (ker p) :=
  ⟨fun hM => .ker_of_surjective p hp hN.of_succ hM, .of_surjective p hp hN⟩

end

section Exact

variable {M' M M'' : Type u} [AddCommGroup M'] [Module R M'] [AddCommGroup M] [Module R M]
  [AddCommGroup M''] [Module R M''] {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}

/-- In a short exact sequence `0 → M' → M → M'' → 0`, `M'` is the kernel of `g`. -/
noncomputable def kerEquivOfExact (hf : Injective f) (H : Exact f g) : M' ≃ₗ[R] ker g :=
  (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp H).symm)

/-- **Prop. 4.2**: in a short exact sequence `0 → M' → M → M'' → 0`, if `M'` and `M''` are
`n`-presented, so is `M`. -/
theorem IsNPresented.of_exact {n : ℕ} (hf : Injective f) (hg : Surjective g) (H : Exact f g)
    (h' : IsNPresented R n M') (h'' : IsNPresented R n M'') : IsNPresented R n M :=
  .of_ker_of_surjective g hg (h'.of_equiv (kerEquivOfExact hf H)) h''

/-- Two out of three, the quotient (Stacks 064R (2), the « il suffit » of 4.4): if `M` is
`(n+1)`-presented and `M'` is `n`-presented, `M''` is `(n+1)`-presented. -/
theorem IsNPresented.of_exact_right {n : ℕ} (hf : Injective f) (hg : Surjective g)
    (H : Exact f g) (h : IsNPresented R (n + 1) M) (h' : IsNPresented R n M') :
    IsNPresented R (n + 1) M'' :=
  .of_surjective g hg h (h'.of_equiv (kerEquivOfExact hf H))

/-- Two out of three, the subobject (Stacks 064R (3), the « il faut » of 4.4): if `M` is
`n`-presented and `M''` is `(n+1)`-presented, `M'` is `n`-presented. -/
theorem IsNPresented.of_exact_left {n : ℕ} (hf : Injective f) (hg : Surjective g)
    (H : Exact f g) (h : IsNPresented R n M) (h'' : IsNPresented R (n + 1) M'') :
    IsNPresented R n M' :=
  (IsNPresented.ker_of_surjective g hg h h'').of_equiv (kerEquivOfExact hf H).symm

/-- **Prop. 4.4** as on the page: in `0 → R → M₀ → X → 0` with `M₀` `(n+1)`-presented, `X` is
`(n+1)`-presented iff `R` is `n`-presented. -/
theorem IsNPresented.iff_of_exact {n : ℕ} (hf : Injective f) (hg : Surjective g)
    (H : Exact f g) (h : IsNPresented R (n + 1) M) :
    IsNPresented R (n + 1) M'' ↔ IsNPresented R n M' :=
  ⟨fun h'' => .of_exact_left hf hg H h.of_succ h'', .of_exact_right hf hg H h⟩

end Exact

end Grothendieck.IhesSGA6_1_5
